import FCAppendix.Affine.Uniform06.RankRent
import FCAppendix.Finite.PPISubcutoffPairTail
import FCAppendix.Affine.LowBody.FirstCopyBoundary

noncomputable section
namespace FCAppendix.Affine.Uniform06.PureRankCounts

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators

section Product
variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]

theorem iid_count_lt_eq_binomBelow
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Set Ω) (hE : MeasurableSet E) (s : Finset ι) (c : ℕ) :
    (Measure.pi fun _ : ι => μ).real {ω | PiBinomial.count E s ω < c} =
      Bayes.binomBelow s.card (μ.real E) c := by
  classical
  have hunion : {ω : ι → Ω | PiBinomial.count E s ω < c} =
      ⋃ r ∈ Finset.range c, {ω | PiBinomial.count E s ω = r} := by
    ext ω
    simp
  rw [hunion,measureReal_biUnion_finset]
  · unfold Bayes.binomBelow
    exact Finset.sum_congr rfl (fun r _ => PiBinomial.measureReal_count_eq μ E hE s r)
  · intro r _ r' _ hrr'
    exact Set.disjoint_left.mpr fun ω h1 h2 => hrr' (h1.symm.trans h2)
  · intro r _
    exact (PiBinomial.measurable_count E hE s) (measurableSet_singleton r)

theorem main_rank_event_relative
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E B : Set Ω) (hE : MeasurableSet E) (hB : MeasurableSet B)
    (hEB : Disjoint E B) (s : Finset ι) (c : ℕ)
    {θ : ℝ} (hθ : 0 ≤ θ) (hE1 : μ.real E < 1) :
    (1-Real.exp (θ*(c-1:ℕ)-(s.card-(c-1):ℕ)*
      (μ.real B/(1-μ.real E))*(1-Real.exp (-θ))))*
      Bayes.binomBelow s.card (μ.real E) c ≤
        (Measure.pi fun _ : ι => μ).real
          {ω | PiBinomial.count E s ω < c ∧ c ≤ PiBinomial.count B s ω} := by
  let P := Measure.pi fun _ : ι => μ
  let A : Set (ι → Ω) := {ω | PiBinomial.count E s ω < c}
  let C : Set (ι → Ω) := {ω | PiBinomial.count B s ω < c}
  have hC : MeasurableSet C :=
    (PiBinomial.measurable_count B hB s) (measurableSet_Iio (a := c))
  have hdecomp := measureReal_inter_add_sdiff (μ := P) (s := A) hC
  have hbad := PiBinomial.pi_pair_lower_tail_le_exp μ E B hE hB hEB θ hθ s c hE1
  have hA : P.real A = Bayes.binomBelow s.card (μ.real E) c :=
    iid_count_lt_eq_binomBelow μ E hE s c
  have he : A \ C = {ω | PiBinomial.count E s ω < c ∧ c ≤ PiBinomial.count B s ω} := by
    ext ω
    simp only [A,C,Set.mem_sdiff,mem_setOf_eq,not_lt]
  change P.real (A ∩ C) ≤ Real.exp _ * Bayes.binomBelow s.card (μ.real E) c at hbad
  rw [hA,he] at hdecomp
  change (1-Real.exp _)*Bayes.binomBelow s.card (μ.real E) c ≤ _
  nlinarith

end Product

theorem exists_positive_tilt {ρ a : ℝ} (hρ : 0 < ρ) (hgap : ρ < a) :
    ∃ θ γ : ℝ, 0 < θ ∧ 0 < γ ∧
      γ = a*(1-Real.exp (-θ))-ρ*θ := by
  let θ := (a-ρ)/(2*ρ)
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have heq : 2*ρ*θ = a-ρ := by
    dsimp [θ]
    field_simp [hρ.ne']
  have heq' := congrArg (fun z : ℝ => θ*z) heq
  have hex : (1+θ)*Real.exp (-θ) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp θ) (Real.exp_pos (-θ)).le
    rw [← Real.exp_add,add_neg_cancel,Real.exp_zero] at h
    nlinarith
  let γ := a*(1-Real.exp (-θ))-ρ*θ
  have hγ : 0 < γ := by
    have ha : 0 < a := hρ.trans hgap
    have hm := mul_le_mul_of_nonneg_left hex ha.le
    have hstrict : 0 < θ*(a-ρ)/2 := by positivity
    have hp : 0 < (1+θ)*γ := by
      dsimp [γ]
      nlinarith [heq']
    exact pos_of_mul_pos_right hp (by linarith : 0 ≤ 1+θ)
  exact ⟨θ,γ,hθ,hγ,rfl⟩

theorem source_conditional_mean_gap
    {t δ Mstar : ℝ} (ht : t < 1) (_hδ : 0 < δ) (hδ1 : δ < 1)
    (hM : 0 ≤ Mstar) (hguard : Mstar < δ*(1-t)/(1-δ)) :
    (1-δ)/2 < ((1+δ)/2)*((1-t)/2)/((1-t)/2+Mstar) := by
  have hd : 0 < (1-t)/2+Mstar := by linarith
  have hg := (lt_div_iff₀ (sub_pos.mpr hδ1)).mp hguard
  apply (lt_div_iff₀ hd).mpr
  nlinarith

theorem source_relative_exponent
    {m c : ℕ} (hc : 0 < c) (hcm : c ≤ m)
    {t ρ w Mstar θ γ : ℝ}
    (ht : t < 1) (_hρ0 : 0 ≤ ρ) (_hρ1 : ρ ≤ 1)
    (hw : 0 ≤ w) (hwM : w ≤ Mstar) (hθ : 0 ≤ θ)
    (hcap : (c : ℝ) ≤ ρ*m)
    (hγ : γ = (1-ρ)*((1-t)/2)/((1-t)/2+Mstar)*
      (1-Real.exp (-θ))-ρ*θ) :
    θ*(c-1:ℕ)-((m-1)-(c-1):ℕ)*
      (((1-t)/2)/((1-t)/2+w))*(1-Real.exp (-θ)) ≤ -γ*m := by
  have hM : 0 ≤ Mstar := hw.trans hwM
  have hdw : 0 < (1-t)/2+w := by linarith
  have hdM : 0 < (1-t)/2+Mstar := by linarith
  have hq : ((1-t)/2)/((1-t)/2+Mstar) ≤ ((1-t)/2)/((1-t)/2+w) :=
    div_le_div_of_nonneg_left (by linarith) hdw (by linarith)
  have he0 : 0 ≤ 1-Real.exp (-θ) := by
    have he := Real.exp_le_one_iff.mpr (show -θ ≤ 0 by linarith)
    linarith
  have hcm1 : c-1 ≤ m-1 := Nat.sub_le_sub_right hcm 1
  have hn : ((m-1)-(c-1):ℕ) = m-c := by omega
  have hcr : (c-1:ℕ) ≤ (c : ℝ) := by exact_mod_cast Nat.sub_le c 1
  have hmr : ((m-c:ℕ):ℝ) = (m:ℝ)-c := Nat.cast_sub hcm
  have hcount : (1-ρ)*m ≤ ((m-c:ℕ):ℝ) := by rw [hmr]; nlinarith
  have hq0 : 0 ≤ ((1-t)/2)/((1-t)/2+Mstar) := by positivity
  have hmult := mul_le_mul_of_nonneg_right
    (mul_le_mul hcount hq hq0 (Nat.cast_nonneg (m-c))) he0
  rw [hmr] at hmult
  rw [hn,hmr,hγ, mul_div_assoc]
  nlinarith [mul_le_mul_of_nonneg_left (hcr.trans hcap) hθ]

section SourceRow
open LowBody

def sourceRivalLaw (t : ℝ) (G : Measure ℝ) : Measure RowRival :=
  rivalLaw t 0 (1-t) G

theorem sourceRivalLaw_probability {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (G : Measure ℝ) [IsProbabilityMeasure G] :
    IsProbabilityMeasure (sourceRivalLaw t G) :=
  rivalLaw_isProbability t 0 (1-t) ht.1 le_rfl (sub_nonneg.mpr ht.2) (by ring) G

def sourceRank (t : ℝ) (G : Measure ℝ) (b : ℝ) : ℝ := t*G.real (Iic b)

def otherUpper : Set RowRival := {r | r.1=3}

theorem measurableSet_otherUpper : MeasurableSet otherUpper :=
  measurableSet_eq_fun measurable_fst measurable_const

theorem disjoint_higher_other (b : ℝ) : Disjoint (higherAtSet b) otherUpper := by
  apply Set.disjoint_left.mpr
  intro r hr ho
  obtain ⟨k,x⟩ := r
  change k=1 ∨ k=2 ∨ (k=0 ∧ b< x) at hr
  change k=3 at ho
  subst k
  norm_num [Fin.ext_iff] at hr

theorem source_higher_probability {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (G : Measure ℝ) [IsProbabilityMeasure G] (b : ℝ) :
    (sourceRivalLaw t G).real (higherAtSet b) = (1+t)/2-sourceRank t G b := by
  have h := higherAtSet_probability t 0 (1-t) ht le_rfl (sub_nonneg.mpr ht1) G b
  have htail : G.real (Ioi b) = 1-G.real (Iic b) := by
    have hc := probReal_compl_eq_one_sub (μ := G) (s := Iic b) measurableSet_Iic
    simpa only [compl_Iic] using hc
  rw [higherBidProbability,htail] at h
  change (rivalLaw t 0 (1-t) G).real (higherAtSet b) = _
  rw [h,sourceRank]
  ring

theorem source_other_probability {t : ℝ} (ht1 : t ≤ 1)
    (G : Measure ℝ) (_b : ℝ) :
    (sourceRivalLaw t G).real otherUpper = (1-t)/2 := by
  have hl : Measurable (fun x : ℝ => ((0:Fin 4),x)) :=
    measurable_const.prodMk measurable_id
  have hp : (fun x : ℝ => ((0:Fin 4),x)) ⁻¹' otherUpper = ∅ := by
    ext x
    norm_num [otherUpper,Fin.ext_iff]
  have he : sourceRivalLaw t G otherUpper = ENNReal.ofReal ((1-t)/2) := by
    simp only [sourceRivalLaw,rivalLaw,Measure.add_apply,Measure.smul_apply,smul_eq_mul]
    rw [Measure.map_apply hl measurableSet_otherUpper,hp]
    norm_num [Measure.dirac_apply,otherUpper,Set.indicator,Fin.ext_iff]
  rw [measureReal_def,he,ENNReal.toReal_ofReal (by linarith)]

theorem source_main_rank_event_relative {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1)
    (G : Measure ℝ) [IsProbabilityMeasure G] (b : ℝ)
    (N c : ℕ) {θ : ℝ} (hθ : 0 ≤ θ) :
    (1-Real.exp (θ*(c-1:ℕ)-(N-(c-1):ℕ)*
      (((1-t)/2)/((1-t)/2+sourceRank t G b))*(1-Real.exp (-θ))))*
      Rank.pureRank N c ((1+t)/2) (sourceRank t G b) ≤
    (Measure.pi fun _ : Fin N => sourceRivalLaw t G).real
      {ω | PiBinomial.count (higherAtSet b) Finset.univ ω < c ∧
        c ≤ PiBinomial.count otherUpper Finset.univ ω} := by
  letI := sourceRivalLaw_probability ⟨ht,ht1.le⟩ G
  have hw : 0 ≤ sourceRank t G b := mul_nonneg ht measureReal_nonneg
  have hE1 : (sourceRivalLaw t G).real (higherAtSet b) < 1 := by
    rw [source_higher_probability ht ht1.le G b]
    linarith
  have h := main_rank_event_relative (sourceRivalLaw t G)
    (higherAtSet b) otherUpper (measurableSet_higherAtSet b)
    measurableSet_otherUpper (disjoint_higher_other b)
    (Finset.univ : Finset (Fin N)) c hθ hE1
  simpa only [Finset.card_univ,Fintype.card_fin,source_higher_probability ht ht1.le G b,
    source_other_probability ht1.le G b,
    show 1-((1+t)/2-sourceRank t G b)=(1-t)/2+sourceRank t G b by ring,
    Rank.pureRank] using h

end SourceRow
end FCAppendix.Affine.Uniform06.PureRankCounts
