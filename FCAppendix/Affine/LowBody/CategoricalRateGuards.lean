import FCAppendix.Affine.LowBody.BinomialBoundary
import FCAppendix.Affine.LowBody.CategoricalTails

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory Set Filter Topology Real
open scoped BigOperators

def jointObjective (s a h ρ t : ℝ) : ℝ :=
  2*ρ*t-log (a*exp (2*t)+h*exp t+s)

def jointRate (s a h ρ : ℝ) : ℝ :=
  sSup (jointObjective s a h ρ '' Iio 0)

theorem exists_negative_joint_tilt (s a h ρ I : ℝ)
    (hgap : 2*I<jointRate s a h ρ) :
    ∃t : ℝ,t<0 ∧ 2*I<jointObjective s a h ρ t := by
  by_contra hn
  have hle : jointRate s a h ρ≤2*I := by
    apply csSup_le
    · exact ⟨jointObjective s a h ρ (-1),⟨-1,by norm_num,rfl⟩⟩
    · rintro _ ⟨t,ht,rfl⟩
      exact le_of_not_gt (fun he=>hn ⟨t,ht,he⟩)
  linarith

lemma binaryKL_nonneg {ρ p : ℝ} (hp0 : 0<p) (hp1 : p<1)
    (hρ0 : 0<ρ) (hρ1 : ρ<1) : 0≤Ample.binaryKL ρ p := by
  simpa using Ample.binary_objective_le hp0 hp1 hρ0 hρ1 0

lemma tendsto_trials_fraction (k : ℕ) :
    Tendsto (fun m : ℕ=>((m-k:ℕ):ℝ)/(m:ℝ)) atTop (𝓝 1) := by
  have hh: Tendsto (fun m : ℕ=>(1:ℝ)-(k:ℝ)/(m:ℝ)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (k:ℝ))
  apply hh.congr'
  filter_upwards [eventually_ge_atTop k,eventually_gt_atTop (0:ℕ)] with m hm hm0
  rw [Nat.cast_sub hm]
  have hmR : (m:ℝ)≠0 := (Nat.cast_pos.mpr hm0).ne'
  field_simp

lemma tendsto_boundary_fraction (c : ℕ→ℕ) (ρ : ℝ) (hρ : 0<ρ)
    (hc : Tendsto (fun m=>(c m:ℝ)/(m:ℝ)) atTop (𝓝 ρ)) :
    Tendsto (fun m=>((c m-1:ℕ):ℝ)/(m:ℝ)) atTop (𝓝 ρ) := by
  have hh : Tendsto (fun m=>(c m:ℝ)/(m:ℝ)-(1:ℝ)/(m:ℝ)) atTop (𝓝 ρ) := by
    simpa using hc.sub (tendsto_const_div_atTop_nhds_zero_nat 1)
  apply hh.congr'
  filter_upwards [hc.eventually_const_lt hρ,eventually_gt_atTop (0:ℕ)] with m hc0 hm0
  have hmR : (0:ℝ) < m := Nat.cast_pos.mpr hm0
  have hcR : (0:ℝ)<c m := (div_pos_iff_of_pos_right hmR).mp hc0
  have hc1 : 1≤c m := Nat.cast_pos.mp hcR
  rw [Nat.cast_sub hc1]
  push_cast
  ring

lemma tendsto_boundary_trials_fraction (c : ℕ→ℕ) (ρ : ℝ) (hρ : 0<ρ)
    (hc : Tendsto (fun m=>(c m:ℝ)/(m:ℝ)) atTop (𝓝 ρ)) (k : ℕ) :
    Tendsto (fun m=>((c m-1:ℕ):ℝ)/((m-k:ℕ):ℝ)) atTop (𝓝 ρ) := by
  have hh := (tendsto_boundary_fraction c ρ hρ hc).div (tendsto_trials_fraction k) one_ne_zero
  change Tendsto (fun m=>(((c m-1:ℕ):ℝ)/(m:ℝ))/(((m-k:ℕ):ℝ)/(m:ℝ)))
    atTop (𝓝 (ρ/1)) at hh
  have hh' : Tendsto (fun m=>(((c m-1:ℕ):ℝ)/(m:ℝ))/(((m-k:ℕ):ℝ)/(m:ℝ)))
      atTop (𝓝 ρ) := by simpa only [div_one,Pi.div_apply] using hh
  apply hh'.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with m hm
  have hmR : (m:ℝ)≠0 := (Nat.cast_pos.mpr hm).ne'
  field_simp

def ell (c : ℕ→ℕ) (p : ℝ) (hp0 : 0≤p) (hp1 : p≤1) (m : ℕ) : ℝ :=
  (IndependentCounts.binomial (m-1) p hp0 hp1).prob (fun r=>r.val≤c m-1)

def boundary (c : ℕ→ℕ) (p : ℝ) (m : ℕ) : ℝ :=
  PiBinomial.pmf (m-2) p (c m-1)

def jointUnderflow (μ : FiniteLaw (Fin 4)) (c : ℕ→ℕ) (k m : ℕ) : ℝ :=
  (CommonList.iid μ (m-k)).prob (BothUnderflow (c m))

theorem eventually_binomial_lower (c : ℕ→ℕ) (p ρ : ℝ)
    (hp0 : 0<p) (hp1 : p<1) (hρ0 : 0<ρ) (hρ1 : ρ<1)
    (hc : Tendsto (fun m=>(c m:ℝ)/(m:ℝ)) atTop (𝓝 ρ))
    (r : ℝ) (hr : Ample.binaryKL ρ p<r) :
    ∀ᶠ m : ℕ in atTop, exp (-(m:ℝ)*r)≤ell c p hp0.le hp1.le m ∧
      exp (-(m:ℝ)*r)≤boundary c p m := by
  have h1:=eventually_pmf_exponential_lower (fun m=>m-1) (fun m=>c m-1) p ρ
    hp0 hp1 hρ0 hρ1 (tendsto_sub_atTop_nat 1) (tendsto_trials_fraction 1)
    (tendsto_boundary_trials_fraction c ρ hρ0 hc 1) r hr
  have h2:=eventually_pmf_exponential_lower (fun m=>m-2) (fun m=>c m-1) p ρ
    hp0 hp1 hρ0 hρ1 (tendsto_sub_atTop_nat 2) (tendsto_trials_fraction 2)
    (tendsto_boundary_trials_fraction c ρ hρ0 hc 2) r hr
  have hK: ∀ᶠ m : ℕ in atTop,c m-1 ≤ m-1 := by
    have he := (tendsto_boundary_trials_fraction c ρ hρ0 hc 1).eventually_lt_const hρ1
    filter_upwards [he,eventually_gt_atTop (1:ℕ)] with m hm hm1
    have hN : (0:ℝ)<((m-1:ℕ):ℝ) := Nat.cast_pos.mpr (by omega)
    exact (Nat.cast_lt.mp ((div_lt_one hN).mp hm)).le
  filter_upwards [h1,h2,hK] with m hm1 hm2 hKm
  exact ⟨hm1.trans (pmf_le_lower_tail (m-1) (c m-1) p hp0.le hp1.le hKm),hm2⟩

theorem eventually_joint_upper (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h)
    (hsum : s+a+h=1) (G : Measure ℝ) [IsProbabilityMeasure G]
    (c : ℕ→ℕ) (ρ : ℝ)
    (hc : Tendsto (fun m=>(c m:ℝ)/(m:ℝ)) atTop (𝓝 ρ))
    (k : ℕ) (t : ℝ) (ht : t≤0) (v : ℝ) (hv : v<jointObjective s a h ρ t) :
    ∀ᶠ m : ℕ in atTop,
      jointUnderflow (categoryLaw s a h hs ha hh hsum G) c k m≤exp (-(m:ℝ)*v) := by
  let Z:=a*exp (2*t)+h*exp t+s
  have hl : Tendsto (fun m : ℕ=>(-2*t)*((c m:ℝ)/(m:ℝ))+
      (((m-k:ℕ):ℝ)/(m:ℝ))*log Z) atTop (𝓝 (-jointObjective s a h ρ t)) := by
    convert (hc.const_mul (-2*t)).add ((tendsto_trials_fraction k).mul_const (log Z)) using 1
    dsimp [jointObjective,Z]
    ring
  have he := hl.eventually_lt_const (show -jointObjective s a h ρ t< -v by linarith)
  filter_upwards [he,eventually_gt_atTop (0:ℕ)] with m hem hm
  have hmR : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hchern := bothUnderflow_chernoff s a h hs ha hh hsum G (m-k) (c m) t ht
  apply hchern.trans
  apply Real.exp_le_exp.mpr
  have hmul:=mul_lt_mul_of_pos_left hem hmR
  have hid : (m:ℝ)*((-2*t)*((c m:ℝ)/(m:ℝ))+
      (((m-k:ℕ):ℝ)/(m:ℝ))*log Z)= -2*t*c m+((m-k:ℕ):ℝ)*log Z := by
    field_simp
  rw [hid] at hmul
  simpa only [mul_neg,neg_mul] using hmul.le

theorem eventually_guards_of_exponential_bounds (L H D E : ℕ→ℝ) (η r v : ℝ)
    (hη : 0≤η) (hr : 0<r) (hgap : 2*r<v)
    (hE : ∀m,0≤E m)
    (hlo : ∀ᶠ m : ℕ in atTop,exp (-(m:ℝ)*r)≤L m ∧ exp (-(m:ℝ)*r)≤H m)
    (hup : ∀ᶠ m : ℕ in atTop,D m≤exp (-(m:ℝ)*v) ∧ E m≤exp (-(m:ℝ)*v)) :
    ∀ᶠ m : ℕ in atTop,0<L m ∧ E m<H m ∧ D m≤L m/4 ∧
      8*η*((m-1:ℕ):ℝ)*E m/(L m*(H m-E m))<1/2 := by
  have hvr : 0<v-r := by linarith
  have hg : 0<v-2*r := by linarith
  have hmTop : Tendsto (fun m : ℕ=>(m:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun m : ℕ=>exp (-(m:ℝ)*(v-r))) atTop (𝓝 0) := by
    convert Real.tendsto_exp_neg_atTop_nhds_zero.comp (hmTop.const_mul_atTop hvr) using 1
    funext m
    congr 1
    ring
  have hpoly : Tendsto (fun m : ℕ=>16*η*(m:ℝ)*exp (-(m:ℝ)*(v-2*r))) atTop (𝓝 0) := by
    have he := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      (hmTop.const_mul_atTop hg)
    have he' := he.const_mul (16*η/(v-2*r))
    convert he' using 1
    · funext m
      simp only [Function.comp_apply,pow_one]
      field_simp
    · simp
  filter_upwards [hlo,hup,hratio.eventually_lt_const (by norm_num : (0:ℝ)<1/4),
      hpoly.eventually_lt_const (by norm_num : (0:ℝ)<1/2)] with m hl hu heps hsmall
  let A:=exp (-(m:ℝ)*r)
  let B:=exp (-(m:ℝ)*v)
  have hA : 0<A := exp_pos _
  have hB : 0<B := exp_pos _
  have hL : 0<L m := hA.trans_le hl.1
  have hH : 0<H m := hA.trans_le hl.2
  have hBA : B=exp (-(m:ℝ)*(v-r))*A := by
    dsimp [A,B]
    rw [←exp_add]
    congr 1
    ring
  have hBsmall : B<A/4 := by
    rw [hBA]
    nlinarith [mul_lt_mul_of_pos_right heps hA]
  have hEsmall : E m<H m/2 := by linarith [hu.2,hl.2]
  have hdiff : 0<H m-E m := by linarith
  have hden : 0<L m*(H m-E m) := mul_pos hL hdiff
  have hBB : B=exp (-(m:ℝ)*(v-2*r))*A^2 := by
    dsimp [A,B]
    rw [pow_two,←exp_add,←exp_add]
    congr 1
    ring
  have hnum : 8*η*((m-1:ℕ):ℝ)*E m≤8*η*(m:ℝ)*B := by
    have hmle : ((m-1:ℕ):ℝ)≤(m:ℝ) := Nat.cast_le.mpr (Nat.sub_le _ _)
    have h1:=mul_le_mul_of_nonneg_right hmle (hE m)
    have h2:=mul_le_mul_of_nonneg_left hu.2 (Nat.cast_nonneg m : (0:ℝ) ≤ m)
    have h3:=mul_le_mul_of_nonneg_left (h1.trans h2) (show (0:ℝ)≤8*η by positivity)
    simpa only [mul_assoc] using h3
  have hsmallB : 8*η*(m:ℝ)*B<A^2/4 := by
    rw [hBB]
    nlinarith [mul_lt_mul_of_pos_right hsmall (sq_pos_of_pos hA)]
  have hdenA : A^2/4≤(1/2:ℝ)*(L m*(H m-E m)) := by
    have hh : A/2≤H m-E m := by linarith [hl.2]
    have hprod := mul_le_mul hl.1 hh (by positivity : 0≤A/2) hL.le
    nlinarith
  refine ⟨hL,by linarith,?_,?_⟩
  · linarith [hu.1,hl.1]
  · exact (div_lt_iff₀ hden).2 (hnum.trans_lt (hsmallB.trans_le hdenA))

theorem eventually_source_guards (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h)
    (hsum : s+a+h=1) (G : Measure ℝ) [IsProbabilityMeasure G]
    (c : ℕ→ℕ) (ρ η : ℝ) (hη : 0≤η)
    (hp0 : 0<1-h/2) (hp1 : 1-h/2<1) (hρ0 : 0<ρ) (hρp : ρ<1-h/2)
    (hc : Tendsto (fun m=>(c m:ℝ)/(m:ℝ)) atTop (𝓝 ρ))
    (hgap : 2*Ample.binaryKL ρ (1-h/2)<jointRate s a h ρ) :
    let μ:=categoryLaw s a h hs ha hh hsum G
    ∀ᶠ m : ℕ in atTop,
      0<ell c (1-h/2) hp0.le hp1.le m ∧
      jointUnderflow μ c 2 m<boundary c (1-h/2) m ∧
      jointUnderflow μ c 1 m≤ell c (1-h/2) hp0.le hp1.le m/4 ∧
      8*η*((m-1:ℕ):ℝ)*jointUnderflow μ c 2 m/
        (ell c (1-h/2) hp0.le hp1.le m*(boundary c (1-h/2) m-jointUnderflow μ c 2 m))<1/2 := by
  let p:=1-h/2
  let I:=Ample.binaryKL ρ p
  let μ:=categoryLaw s a h hs ha hh hsum G
  have hρ1 : ρ<1 := hρp.trans hp1
  have hI : 0≤I := binaryKL_nonneg hp0 hp1 hρ0 hρ1
  obtain ⟨t,ht,hb⟩:=exists_negative_joint_tilt s a h ρ I hgap
  let b:=jointObjective s a h ρ t
  let δ:=(b-2*I)/8
  let r:=I+δ
  let v:=b-δ
  have hδ : 0<δ := by dsimp [δ,b]; linarith
  have hrI : I<r := by dsimp [r]; linarith
  have hr : 0<r := hI.trans_lt hrI
  have hv : v<b := by dsimp [v]; linarith
  have hvr : 2*r<v := by dsimp [r,v,δ]; linarith
  have hl:=eventually_binomial_lower c p ρ hp0 hp1 hρ0 hρ1 hc r hrI
  have hd:=eventually_joint_upper s a h hs ha hh hsum G c ρ hc 1 t ht.le v hv
  have he:=eventually_joint_upper s a h hs ha hh hsum G c ρ hc 2 t ht.le v hv
  have hu : ∀ᶠ m : ℕ in atTop,jointUnderflow μ c 1 m≤exp (-(m:ℝ)*v) ∧
      jointUnderflow μ c 2 m≤exp (-(m:ℝ)*v) := hd.and he
  exact eventually_guards_of_exponential_bounds
    (ell c p hp0.le hp1.le) (boundary c p)
    (jointUnderflow μ c 1) (jointUnderflow μ c 2) η r v hη hr hvr
    (fun m=>(CommonList.iid μ (m-2)).prob_nonneg _) hl hu

end FCAppendix.Affine.LowBody
