import FCAppendix.Affine.Tail04.ActualGuardMarginals
import FCAppendix.Affine.Tail04.FavoredOrdinaryCarrier

noncomputable section
namespace FCAppendix.Affine.Tail04.ActiveGainUniformModulus
open MeasureTheory Set Classical
open TypicalFinitePromotion ActualFallbackPromotion CompactPromotionErrors
open ActualActiveFiniteGain ActualGuardMarginals EqualPrivateSignal SortedAllNoise
open AtypicalFittingFiniteLoss
open scoped BigOperators

def flagFloor (e0 F C : ℝ) : ℝ := e0*((F-C)/(F-1))^2

lemma flagFloor_pos {e0 F C : ℝ} (he : 0< e0) (hF : 1< F) (hC : C< F) :
    0< flagFloor e0 F C := by
  exact mul_pos he (sq_pos_of_pos (div_pos (sub_pos.mpr hC) (sub_pos.mpr hF)))

theorem sourceFlagProb_ge_floor {N : ℕ} {e0 F C : ℝ}
    (he0 : 0≤ e0) (he1 : e0≤1) (hF : 1< F) (hCF : C≤ F)
    (b : Fin N → ℝ) (i : Fin N) (hbi : b i∈Icc (1:ℝ) C) :
    flagFloor e0 F C≤ sourceFlagProb e0 F b i := by
  rw [sourceFlagProb_eq he0 he1 hF b i ⟨hbi.1,hbi.2.trans hCF⟩]
  have hden : 0< F-1 := sub_pos.mpr hF
  have hlo : 0≤(F-C)/(F-1) := div_nonneg (sub_nonneg.mpr hCF) hden.le
  have he : (F-C)/(F-1)≤(F-b i)/(F-1) :=
    div_le_div_of_nonneg_right (by linarith [hbi.2]) hden.le
  exact mul_le_mul_of_nonneg_left (by nlinarith : ((F-C)/(F-1))^2≤((F-b i)/(F-1))^2) he0

def populationCoefficient (m : ℕ) (ξ width e0 F C : ℝ) : ℝ :=
  (1-2*ξ)*(sourceQmin ξ width)^2*(flagFloor e0 F C)^2/((m:ℝ)*((m:ℝ)+1))

lemma populationCoefficient_mono_flag {m : ℕ} {ξ width e e' F C : ℝ}
    (hξ : ξ≤1/2) (he : 0≤ e) (hee' : e≤ e') :
    populationCoefficient m ξ width e F C≤ populationCoefficient m ξ width e' F C := by
  have hp0 : 0≤ flagFloor e F C := by unfold flagFloor;positivity
  have hpp : flagFloor e F C≤ flagFloor e' F C :=
    mul_le_mul_of_nonneg_right hee' (sq_nonneg _)
  have hs : (flagFloor e F C)^2≤(flagFloor e' F C)^2 := by nlinarith
  unfold populationCoefficient
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hs (by nlinarith [sq_nonneg (sourceQmin ξ width)])) (by positivity)

lemma populationCoefficient_pos {m : ℕ} {ξ width e0 F C : ℝ}
    (hm : 0< m) (hξ : 0< ξ) (hξh : ξ<1/2) (hw : 0< width)
    (he : 0< e0) (hF : 1< F) (hCF : C< F) :
    0< populationCoefficient m ξ width e0 F C := by
  have hq := sourceQmin_pos hξ hw
  have hp := flagFloor_pos he hF hCF
  have hη : 0<1-2*ξ := by linarith
  unfold populationCoefficient
  positivity

variable {N : ℕ} [Nonempty (Fin N)]

def freezeFocal (b : Fin N → ℝ) (i : Fin N) (y : ℝ) : Fin N → ℝ :=
  freeze b (b i) y (b i)

omit [Nonempty (Fin N)] in
lemma freezeFocal_self (b : Fin N → ℝ) (i : Fin N) (y : ℝ) (hy : b i≤ y) :
    freezeFocal b i y i=b i := by simp [freezeFocal,freeze,hy]

omit [Nonempty (Fin N)] in
lemma freezeFocal_ties (b : Fin N → ℝ) (i : Fin N) (y : ℝ) (hy : b i≤ y)
    (j : Fin N) (hj : b j∈Icc (b i) y) : freezeFocal b i y i=freezeFocal b i y j :=
  freeze_ties b i (b i) y (b i) le_rfl hy j hj

omit [Nonempty (Fin N)] in
lemma freezeFocal_bounds {B : ℝ} (b : Fin N → ℝ) (i : Fin N) (y : ℝ)
    (hb : ∀ j,b j∈Icc (1:ℝ) B) (j : Fin N) : freezeFocal b i y j∈Icc (1:ℝ) B :=
  freeze_mem b (b i) y (b i) 1 B hb (hb i) j

omit [Nonempty (Fin N)] in
lemma freezeFocal_close (b : Fin N → ℝ) (i : Fin N) (y : ℝ) (hy : b i≤ y) (j : Fin N) :
    |freezeFocal b i y j-b j|≤ y-b i :=
  freeze_variation_bound b (b i) y (b i) (y-b i) (sub_nonneg.mpr hy) (by linarith) (by linarith) j

omit [Nonempty (Fin N)] in
lemma update_freezeFocal_close (b : Fin N → ℝ) (i : Fin N) (y : ℝ) (hy : b i≤ y) (j : Fin N) :
    |Function.update b i y j-freezeFocal b i y j|≤ y-b i := by
  by_cases hji : j=i
  · subst j
    rw [Function.update_self,freezeFocal_self b i y hy,abs_of_nonneg (sub_nonneg.mpr hy)]
  · rw [Function.update_of_ne hji,abs_sub_comm]
    exact freezeFocal_close b i y hy j

lemma rankDenominator_ge_one : 1≤ Hybrid.rankDenominator (Fin N) := by
  have hN0 : 0< N := by simpa using (Fintype.card_pos : 0< Fintype.card (Fin N))
  have hN : 1≤ N := hN0
  have hNr : (1:ℝ)≤ N := by exact_mod_cast hN
  unfold Hybrid.rankDenominator
  simp only [Fintype.card_fin]
  nlinarith

lemma coefficient_lower {m : ℕ} {ξ width e0 F C v B p βd βa : ℝ}
    (hcard : N≤ m) (hξ : 0< ξ) (hξh : ξ≤1/2) (hw : 0< width)
    (hp0 : 0≤ flagFloor e0 F C) (hp : flagFloor e0 F C≤ p)
    (hv : 0≤ v) (hB : 0≤ B) (hBC : B≤ C) (hβd : 0≤ βd) (hβa : 0≤ βa) :
    populationCoefficient m ξ width e0 F C-(v+2*C+1)*(βd+βa)≤
      ((1-2*ξ)*(sourceQmin ξ width)^2)*(p^2/2-βd)/Hybrid.rankDenominator (Fin N)-
        (v+2*B)*βa := by
  let g := (1-2*ξ)*(sourceQmin ξ width)^2
  have hq := sourceQmin_pos hξ hw
  have hq1 : sourceQmin ξ width≤1 := min_le_left _ _
  have heta : 0≤1-2*ξ := by linarith
  have hg0 : 0≤ g := mul_nonneg heta (sq_nonneg _)
  have hg1 : g≤1 := by
    have hqs : (sourceQmin ξ width)^2≤1 := by nlinarith
    dsimp [g]
    nlinarith
  have hden := rankDenominator_ge_one (N:=N)
  have hp2 : (flagFloor e0 F C)^2≤ p^2 := by nlinarith
  have hr := rank_coefficient_population_lower (ι:=Fin N) (m:=m) (by simpa using hcard)
  have hpos1 := mul_le_mul_of_nonneg_left hr (mul_nonneg hg0 (sq_nonneg (flagFloor e0 F C)))
  have hpos2 := mul_le_mul_of_nonneg_left hp2 hg0
  have hpos3 := div_le_div_of_nonneg_right hpos2 (by positivity : 0≤2*Hybrid.rankDenominator (Fin N))
  have hbad : g/Hybrid.rankDenominator (Fin N)≤1 :=
    (div_le_one Hybrid.rankDenominator_pos).mpr (hg1.trans hden)
  have hneg := mul_le_mul_of_nonneg_right hbad hβd
  have hfall := mul_le_mul_of_nonneg_right (show v+2*B≤ v+2*C from by linarith) hβa
  have hC : 0≤ C := hB.trans hBC
  have hextra := mul_nonneg (show 0≤ v+2*C by positivity) hβd
  have he1 : g*(flagFloor e0 F C)^2*(1/((m:ℝ)*((m:ℝ)+1)))=
      populationCoefficient m ξ width e0 F C := by unfold populationCoefficient;dsimp [g];ring
  have he2 : g*(flagFloor e0 F C)^2*(1/(2*Hybrid.rankDenominator (Fin N)))=
      g*(flagFloor e0 F C)^2/(2*Hybrid.rankDenominator (Fin N)) := by ring
  rw [he1,he2] at hpos1
  have he3 : g*(p^2/2-βd)/Hybrid.rankDenominator (Fin N)=
      g*p^2/(2*Hybrid.rankDenominator (Fin N))-(g/Hybrid.rankDenominator (Fin N))*βd := by ring
  change _≤ g*(p^2/2-βd)/Hybrid.rankDenominator (Fin N)-(v+2*B)*βa
  rw [he3]
  nlinarith only [hpos1,hpos3,hneg,hfall,hextra,hβa]

theorem exists_actual_finite_gain_radius (H0 H1 c m : ℕ) (hcard : N≤ m)
    {ξ R width e0 F C vlo vhi : ℝ}
    (hξ : 0< ξ) (hξh : ξ≤1/2) (hw : 0< width) (he0 : 0≤ e0) (he1 : e0≤1)
    (hF : 1< F) (hCF : C≤ F) (reg lowPresent : Bool)
    (ν0 : FiniteLaw (Marks H0)) (ν1 : FiniteLaw (Marks H1)) (i : Fin N)
    {e : ℝ} (he : 0< e) :
    ∃ δ : ℝ,0< δ ∧ ∀ B∈Icc (1:ℝ) C,∀ Rp∈Icc (0:ℝ) 1,∀ v∈Icc vlo vhi,
      (1-ξ)*B<1 → ∀ b : Fin N → ℝ,(∀ j,b j∈Icc (1:ℝ) B) →
      (∀ j k,j≠k → b j≠b k) → b i≤ v →
      ∀ y : ℝ,b i< y → y≤ B → y-b i< δ →
      let d := freezeFocal b i y
      let cut := effectivePhi lowPresent (TypicalGuardStatistics.phi N H0 H1 c ξ B R Rp width reg ν0 ν1)
      let a := Function.update b i y
      populationCoefficient m ξ width e0 F C*crossingCount b i y-
        (vhi+2*C+1)*(badWeightProbability cut e0 F d+badWeightProbability cut e0 F a)*
          crossingCount b i y-2*e-2*(y-b i)≤
      affineCountUtility (UnequalNoisyCountPayoff.rawCount H0 H1 c ξ B R Rp width e0 F
        reg lowPresent ν0 ν1 a i) v y (1-2*ξ) (by linarith) (by linarith)-
      affineCountUtility (UnequalNoisyCountPayoff.rawCount H0 H1 c ξ B R Rp width e0 F
        reg lowPresent ν0 ν1 b i) v (b i) (1-2*ξ) (by linarith) (by linarith) := by
  obtain ⟨δ,hδ,hmod⟩ := exists_actual_variation_modulus N H0 H1 c ξ R width e0 F
    (1-2*ξ) (by linarith) (by linarith) reg lowPresent ν0 ν1 i 1 C 0 1 vlo vhi C he
  refine ⟨δ,hδ,?_⟩
  intro B hB Rp hRp v hv hsep b hb hno hiv y hy hyB hδbid
  dsimp only
  let d := freezeFocal b i y
  let a := Function.update b i y
  let P := NativeTypicalCount.countParameters N H0 H1 c ξ reg ν0 ν1
  let cut := effectivePhi lowPresent (TypicalGuardStatistics.phi N H0 H1 c ξ B R Rp width reg ν0 ν1)
  let K := sortedFallback N H0 H1 c ξ ν0 ν1 b i
  have hd (j : Fin N) : d j∈Icc (1:ℝ) B := freezeFocal_bounds b i y hb j
  have ha (j : Fin N) : a j∈Icc (1:ℝ) B := by
    by_cases hji : j=i
    · subst j
      simpa only [a,Function.update_self] using
        (show y∈Icc (1:ℝ) B from ⟨(hb i).1.trans hy.le,hyB⟩)
    · simpa only [a,Function.update_of_ne hji] using hb j
  let bb : Fin N → Icc (1:ℝ) C := fun j => ⟨b j,(hb j).1,(hb j).2.trans hB.2⟩
  let dd : Fin N → Icc (1:ℝ) C := fun j => ⟨d j,(hd j).1,(hd j).2.trans hB.2⟩
  let aa : Fin N → Icc (1:ℝ) C := fun j => ⟨a j,(ha j).1,(ha j).2.trans hB.2⟩
  have hbd : dist bb dd< δ := (dist_pi_lt_iff hδ).mpr (fun j => by
    change |b j-d j|< δ
    rw [abs_sub_comm]
    exact (freezeFocal_close b i y hy.le j).trans_lt hδbid)
  have had : dist aa dd< δ := (dist_pi_lt_iff hδ).mpr (fun j => by
    change |a j-d j|< δ
    exact (update_freezeFocal_close b i y hy.le j).trans_lt hδbid)
  have he0' := (hmod ⟨B,hB⟩ ⟨Rp,hRp⟩ ⟨v,hv⟩ bb dd hbd K).le
  have he1' := (hmod ⟨B,hB⟩ ⟨Rp,hRp⟩ ⟨v,hv⟩ aa dd had K).le
  have hg := actual_raw_finite_gain H0 H1 c (R:=R) (Rp:=Rp) (width:=width)
    (e0:=e0) (F:=F) reg lowPresent ν0 ν1 hξ.le hξh hsep
    b d hb hno i hiv y hy hyB (freezeFocal_ties b i y hy.le)
    (L:=1) (qmin:=sourceQmin ξ width) (by norm_num) (sourceQmin_pos hξ hw).le
    (by simpa only [d,freezeFocal_self b i y hy.le] using hiv)
    (by simpa only [d,freezeFocal_self b i y hy.le] using (hb i).1)
  dsimp only at hg
  rw [badProbability_eq_badWeight H0 H1 c reg lowPresent ν0 ν1 hξ hw d i (hd i).1] at hg
  have hp := sourceFlagProb_ge_floor he0 he1 hF hCF d i ⟨(hd i).1,(hd i).2.trans hB.2⟩
  have hp0 : 0≤ flagFloor e0 F C := by unfold flagFloor;positivity
  have hv0 : 0≤ v := (by norm_num : (0:ℝ)≤1).trans ((hb i).1.trans hiv)
  have hc := coefficient_lower (N:=N) (βd:=badWeightProbability cut e0 F d)
    (βa:=badWeightProbability cut e0 F a) hcard hξ hξh hw hp0 hp hv0
    (by linarith [hB.1] : 0≤ B) hB.2
    (FiniteLaw.prob_nonneg _ _) (FiniteLaw.prob_nonneg _ _)
  have hvdiff := mul_nonneg (sub_nonneg.mpr hv.2)
    (add_nonneg (show 0≤ badWeightProbability cut e0 F d from FiniteLaw.prob_nonneg _ _)
      (show 0≤ badWeightProbability cut e0 F a from FiniteLaw.prob_nonneg _ _))
  have hcross := mul_le_mul_of_nonneg_right (show
      populationCoefficient m ξ width e0 F C-(vhi+2*C+1)*
        (badWeightProbability cut e0 F d+badWeightProbability cut e0 F a)≤
      ((1-2*ξ)*(sourceQmin ξ width)^2)*
        ((sourceFlagProb e0 F d i)^2/2-badWeightProbability cut e0 F d)/
          Hybrid.rankDenominator (Fin N)-(v+2*B)*badWeightProbability cut e0 F a from by
        linarith [hc]) (crossingCount_nonneg b i y)
  dsimp only [P,cut,K,bb,dd,aa,a,d] at he0' he1' hcross hg ⊢
  simp only [mul_one] at hg
  nlinarith only [hg,hcross,he0',he1']

end FCAppendix.Affine.Tail04.ActiveGainUniformModulus
