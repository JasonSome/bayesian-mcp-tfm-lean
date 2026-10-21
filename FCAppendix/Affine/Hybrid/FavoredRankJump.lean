import FCAppendix.Affine.Hybrid.FavoredPayoffContinuity

noncomputable section
namespace FCAppendix.Affine.Hybrid
open Set Filter Topology
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def tiedRivals (b : ι→ℝ) (i : ι) : Finset ι :=
  Finset.univ.filter (fun j=>j≠i ∧ b j=b i)

lemma not_mem_tiedRivals (b : ι→ℝ) (i : ι) : i∉tiedRivals b i := by
  simp [tiedRivals]

def rightRankScore (b : ι→ℝ) (i t u : ι) : ℝ :=
  rankScore b t u+
    (if t=i then if u∈tiedRivals b i then 1/2 else 0 else 0)-
    (if u=i then if t∈tiedRivals b i then 1/2 else 0 else 0)

lemma eventually_rankScore_right (b : ι→ℝ) (i t u : ι) :
    ∀ᶠx in 𝓝[>] b i,rankScore (Function.update b i x) t u=rightRankScore b i t u := by
  have hx : ∀ᶠx in 𝓝[>] b i,b i<x := self_mem_nhdsWithin
  by_cases ht : t=i
  · subst t
    by_cases hu : u=i
    · subst u
      exact Eventually.of_forall (fun x=>by simp [rankScore,rightRankScore,not_mem_tiedRivals])
    · rcases lt_trichotomy (b u) (b i) with hlt | heq | hgt
      · filter_upwards [hx] with x hxx
        have hux:=hlt.trans hxx
        simp [rankScore,rightRankScore,tiedRivals,hu,hlt,ne_of_lt hlt,hux]
      · filter_upwards [hx] with x hxx
        norm_num [rankScore,rightRankScore,tiedRivals,hu,heq,hxx]
      · have hx' : ∀ᶠx in 𝓝[>] b i,x<b u :=
          (show ∀ᶠx in 𝓝 (b i), x<b u from Iio_mem_nhds hgt).filter_mono nhdsWithin_le_nhds
        filter_upwards [hx'] with x hxx
        simp [rankScore,rightRankScore,tiedRivals,hu,hgt,ne_of_gt hgt,hxx,not_lt_of_ge hgt.le,
          not_lt_of_ge hxx.le]
  · by_cases hu : u=i
    · subst u
      rcases lt_trichotomy (b t) (b i) with hlt | heq | hgt
      · filter_upwards [hx] with x hxx
        have htx:=hlt.trans hxx
        simp [rankScore,rightRankScore,tiedRivals,ht,hlt,ne_of_lt hlt,htx,not_lt_of_ge hlt.le,
          not_lt_of_ge htx.le]
      · filter_upwards [hx] with x hxx
        simp [rankScore,rightRankScore,tiedRivals,ht,heq,hxx,not_lt_of_ge hxx.le]
      · have hx' : ∀ᶠx in 𝓝[>] b i,x<b t :=
          (show ∀ᶠx in 𝓝 (b i), x<b t from Iio_mem_nhds hgt).filter_mono nhdsWithin_le_nhds
        filter_upwards [hx'] with x hxx
        simp [rankScore,rightRankScore,tiedRivals,ht,hgt,ne_of_gt hgt,hxx]
    · exact Eventually.of_forall (fun x=>by simp [rankScore,rightRankScore,ht,hu])

def rightRank (b : ι→ℝ) (i t : ι) : ℝ :=
  averageRank b t+(if t=i then ((tiedRivals b i).card:ℝ)/2 else 0)-
    (if t∈tiedRivals b i then 1/2 else 0)

lemma sum_rightRankScore (b : ι→ℝ) (i t : ι) :
    1/2+∑u,rightRankScore b i t u=rightRank b i t := by
  unfold rightRankScore rightRank averageRank
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  have ht : (∑u:ι,if u∈tiedRivals b i then (1/2:ℝ) else 0)=
      (tiedRivals b i).card/2 := by simp [Finset.sum_ite_mem,div_eq_mul_inv]
  rw [ht]
  ring

lemma tendsto_averageRank_right (b : ι→ℝ) (i t : ι) :
    Tendsto (fun x=>averageRank (Function.update b i x) t) (𝓝[>] b i)
      (𝓝 (rightRank b i t)) := by
  rw [←sum_rightRankScore]
  apply tendsto_const_nhds.add
  exact tendsto_finsetSum _ (fun u _=>
    tendsto_const_nhds.congr' ((eventually_rankScore_right b i t u).mono (fun _ hx=>hx.symm)))

lemma rightRank_expect_identity [Nonempty ι] (b : ι→ℝ) (i : ι) (f : ι→ℝ) :
    (∑t,rightRank b i t/rankDenominator ι*f t)=
      (rankLaw b).expect f+
        (∑j∈tiedRivals b i,(f i-f j))/(2*rankDenominator ι) := by
  have h1 : (∑t:ι,(if t=i then ((tiedRivals b i).card:ℝ)/2 else 0)*f t)=
      ((tiedRivals b i).card:ℝ)/2*f i := by simp [ite_mul]
  have h2 : (∑t:ι,(if t∈tiedRivals b i then (1/2:ℝ) else 0)*f t)=
      (∑t∈tiedRivals b i,f t)/2 := by
    simp only [ite_mul,zero_mul,Finset.sum_ite_mem,Finset.univ_inter]
    rw [←Finset.mul_sum]
    ring
  have h3 : (∑j∈tiedRivals b i,(f i-f j))=
      ((tiedRivals b i).card:ℝ)*f i-∑j∈tiedRivals b i,f j := by
    rw [Finset.sum_sub_distrib]
    simp
  unfold rightRank FiniteLaw.expect rankLaw
  simp only [add_div,sub_div,add_mul,sub_mul]
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib]
  have hd : ∀g:ι→ℝ,(∑t,g t/rankDenominator ι*f t)=
      (∑t,g t*f t)/rankDenominator ι := by intro g; simp [div_mul_eq_mul_div,Finset.sum_div]
  rw [hd,hd,hd,h1,h2,h3]
  ring

theorem tendsto_sourceOwnerPayoff_right [Nonempty ι] (xi : ℝ)
    (eta v : ℝ) (b : ι→ℝ) (r K1 K2 : ℕ) (i : ι)
    (hN : 2≤Fintype.card ι) (hK0 : 0<K1+K2)
    (hKN : K1+K2<Fintype.card ι) (hb : ∀j,0<b j) :
    Tendsto (fun x=>sourceOwnerPayoff xi eta v (Function.update b i x) r K1 K2 i)
      (𝓝[>] b i) (𝓝 (sourceOwnerPayoff xi eta v b r K1 K2 i+
        (∑j∈tiedRivals b i,
          (favoredTargetPayoff xi eta v b r (K1+K2) i i-
          favoredTargetPayoff xi eta v b r (K1+K2) i j))/(2*rankDenominator ι))) := by
  have hbcont : Continuous (fun x : ℝ=>Function.update b i x) :=
    continuous_const.update i continuous_id
  have hbval : Function.update b i (b i)=b := Function.update_eq_self i b
  have hf (t : ι) : Tendsto
      (fun x=>favoredTargetPayoff xi eta v (Function.update b i x) r (K1+K2) i t)
      (𝓝[>] b i) (𝓝 (favoredTargetPayoff xi eta v b r (K1+K2) i t)) := by
    have hstart : Tendsto (fun x : ℝ=>Function.update b i x) (𝓝[>] b i) (𝓝 b) := by
      have hh : Tendsto (fun x : ℝ=>Function.update b i x) (𝓝 (b i)) (𝓝 b) := by
        simpa only [hbval] using hbcont.tendsto (b i)
      exact hh.mono_left nhdsWithin_le_nhds
    exact (continuousAt_favoredTargetPayoff xi eta v b r (K1+K2) i t
      hN (by omega) hKN hb).tendsto.comp hstart

  have hs := tendsto_finsetSum Finset.univ (fun t _=>
    ((tendsto_averageRank_right b i t).div_const (rankDenominator ι)).mul (hf t))
  rw [rightRank_expect_identity,←sourceOwnerPayoff_eq_rank xi eta v b r K1 K2 i hN hK0 hKN.le] at hs
  apply hs.congr'
  exact Eventually.of_forall (fun x=>by
    dsimp only
    rw [sourceOwnerPayoff_eq_rank xi eta v _ r K1 K2 i hN hK0 hKN.le]
    rfl)

end FCAppendix.Affine.Hybrid
