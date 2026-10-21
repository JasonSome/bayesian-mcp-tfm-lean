import FCAppendix.Affine.LowBody.Rows
import FCAppendix.Probability.FiniteHoeffding

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Game Set Classical Real
open scoped BigOperators ENNReal

section Law
variable (s a h : ℝ) (hs : 0≤ s) (ha : 0≤ a) (hh : 0≤ h) (hsum : s+a+h=1)
    (G : Measure ℝ) [IsProbabilityMeasure G]

def categoryLaw : FiniteLaw (Fin 4) := by
  letI : IsProbabilityMeasure (rivalLaw s a h G) :=
    rivalLaw_isProbability s a h hs ha hh hsum G
  exact FiniteLaw.ofMeasure (rivalLaw s a h G) Prod.fst measurable_fst

lemma categoryLaw_mass (k : Fin 4) :
    (categoryLaw s a h hs ha hh hsum G).mass k=![s,a,h/2,h/2] k := by
  letI : IsProbabilityMeasure (rivalLaw s a h G) :=
    rivalLaw_isProbability s a h hs ha hh hsum G
  rw [categoryLaw,FiniteLaw.ofMeasure_mass]
  have hlow : Measurable (fun b : ℝ=>((0:Fin 4),b)) := measurable_const.prodMk measurable_id
  have hE : MeasurableSet {z : RowRival | z.1=k} :=
    measurableSet_eq_fun measurable_fst measurable_const
  have hmap : (G.map (fun b : ℝ=>((0:Fin 4),b))) {z : RowRival | z.1=k}=
      if k=0 then 1 else 0 := by
    rw [Measure.map_apply hlow hE]
    by_cases hk : k=0
    · subst k
      simp
    · have h0 : (0:Fin 4)≠k := Ne.symm hk
      simp [h0,hk]
  simp only [rivalLaw,Measure.add_apply,Measure.smul_apply,smul_eq_mul]
  rw [hmap]
  have hh2 : 0≤h/2 := by positivity
  fin_cases k <;> simp [Measure.dirac_apply,Set.indicator,hs,ha,hh2,ENNReal.toReal_ofReal]

lemma categoryLaw_expect (f : Fin 4→ℝ) :
    (categoryLaw s a h hs ha hh hsum G).expect f=
      s*f 0+a*f 1+(h/2)*f 2+(h/2)*f 3 := by
  unfold FiniteLaw.expect
  simp only [categoryLaw_mass]
  simp [Fin.sum_univ_succ]
  ring

def firstHigher (k : Fin 4) : ℕ := if k=1 ∨ k=2 then 1 else 0
def secondHigher (k : Fin 4) : ℕ := if k=1 ∨ k=3 then 1 else 0

def higherTotal (k : Fin 4) : ℝ := firstHigher k+secondHigher k

def BothUnderflow {N : ℕ} (c : ℕ) (ω : Fin N→Fin 4) : Prop :=
  (∑i,firstHigher (ω i))<c ∧ (∑i,secondHigher (ω i))<c

lemma total_eq (k : Fin 4) : higherTotal k=![0,2,1,1] k := by
  fin_cases k <;> norm_num [higherTotal,firstHigher,secondHigher,Fin.ext_iff]

lemma categorical_mgf (t : ℝ) :
    FiniteCramer.Z (categoryLaw s a h hs ha hh hsum G) higherTotal t=
      a*exp (2*t)+h*exp t+s := by
  rw [FiniteCramer.Z,categoryLaw_expect]
  norm_num [higherTotal,firstHigher,secondHigher,Fin.ext_iff]
  ring

theorem bothUnderflow_chernoff (N c : ℕ) (t : ℝ) (ht : t≤0) :
    (CommonList.iid (categoryLaw s a h hs ha hh hsum G) N).prob (BothUnderflow c)≤
      exp (-2*t*c+(N:ℝ)*log (a*exp (2*t)+h*exp t+s)) := by
  have hc := FiniteCramer.iid_chernoff (categoryLaw s a h hs ha hh hsum G)
    higherTotal N t (2*c) (BothUnderflow c) (by
      intro ω hω
      apply mul_le_mul_of_nonpos_left _ ht
      unfold higherTotal
      rw [Finset.sum_add_distrib]
      have h₁ : (∑i,(firstHigher (ω i):ℝ))≤(c:ℝ) := by exact_mod_cast hω.1.le
      have h₂ : (∑i,(secondHigher (ω i):ℝ))≤(c:ℝ) := by exact_mod_cast hω.2.le
      linarith)
  rw [FiniteCramer.cgf,categorical_mgf] at hc
  convert hc using 1
  congr 1
  ring
end Law
end FCAppendix.Affine.LowBody
