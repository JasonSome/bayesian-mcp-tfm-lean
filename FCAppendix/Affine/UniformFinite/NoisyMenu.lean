import FCAppendix.Affine.UniformFinite.SourceProductMenu
import FCAppendix.Affine.UniformFinite.LimitOptimality
import FCAppendix.Affine.UniformFinite.NoisyFixedPoint

noncomputable section
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Filter Topology Classical
open Existence.Distributional
open scoped BigOperators

private theorem noisy_row_integrable (i : Row) (N : ℕ) (eps : unitInterval)
    (pi : Joint i) (v : Value i) (q : unitInterval) (kind : Fin N → Fin 3) :
    Integrable (fun x : (Fin N → Bid i) × unitInterval =>
      rowPayoff i (restrictedLaw i (eps,pi)) (focalRow kind) v
        (focalBids i kind (noisyBid i (eps,((v,q),x.2))) x.1) 0)
      ((rowLaw N (restrictedLaw i (eps,pi)).bidLaw : Measure (Fin N → Bid i)).prod
        (volume : Measure unitInterval)) := by
  have hm : Measurable (fun x : (Fin N → Bid i) × unitInterval =>
      Noisy.rowFunction i eps kind ((pi,(v,q)),x)) :=
    (Noisy.measurable_rowFunction i eps kind).comp (measurable_const.prodMk measurable_id)
  apply (integrable_const (3*Uniform05.t i)).mono' hm.aestronglyMeasurable
  exact ae_of_all _ fun x => by
    simpa only [Real.norm_eq_abs] using
      Noisy.rowFunction_bound i eps kind ((pi,(v,q)),x)

theorem integrable_rawUtility_own_noise (i : Row) (N : ℕ) (eps : unitInterval)
    (pi : Joint i) (v : Value i) (q : unitInterval) :
    Integrable (fun z : unitInterval => rawUtility i N (restrictedLaw i (eps,pi)) v
      (noisyBid i (eps,((v,q),z)))) volume := by
  unfold rawUtility FiniteLaw.expect
  apply integrable_finsetSum
  intro kind _
  exact (noisy_row_integrable i N eps pi v q kind).integral_prod_right.const_mul _

theorem expectedUtility_eq_raw_noise (i : Row) (N : ℕ) (eps : unitInterval)
    (pi : Joint i) (v : Value i) (q : unitInterval) :
    expectedUtility i N eps pi v q =
      ∫z : unitInterval, rawUtility i N (restrictedLaw i (eps,pi)) v
        (noisyBid i (eps,((v,q),z))) := by
  unfold expectedUtility rawUtility FiniteLaw.expect
  rw [integral_finsetSum _ (fun kind _ =>
    (noisy_row_integrable i N eps pi v q kind).integral_prod_right.const_mul _)]
  apply Finset.sum_congr rfl
  intro kind _
  rw [integral_const_mul]
  congr 1
  exact integral_integral_swap (noisy_row_integrable i N eps pi v q kind)

abbrev ProductRoot (i : Row) :=
  Icc ((54 : ℝ)/100*Uniform05.t i) (Uniform05.cap i)

def actualProductRoot (i : Row) (G : Uniform05.RestrictedLaw i) : ProductRoot i :=
  ⟨G.multiplier,G.multiplier_guards.1.le,G.multiplier_guards.2.2.1.le⟩

abbrev ProductBox (i : Row) := Value i × (ProductRoot i × Bid i)

def productBoxPayoff (i : Row) (p : ProductBox i) : ℝ :=
  productPayoff (Uniform05.xi i) p.1 p.2.1 p.2.2

theorem continuous_productBoxPayoff (i : Row) : Continuous (productBoxPayoff i) := by
  have hV : Continuous (fun p : ProductBox i => (p.1:ℝ)) := by fun_prop
  have hL : Continuous (fun p : ProductBox i => (p.2.1:ℝ)) := by fun_prop
  have hB : Continuous (fun p : ProductBox i => (p.2.2:ℝ)) := by fun_prop
  have hp : Continuous (fun p : ProductBox i =>
      ClippedResidual.exposure (Uniform05.xi i) p.2.1 p.2.2) := by
    unfold ClippedResidual.exposure
    apply continuous_const.min
    apply (continuous_const.max (hB.sub hL)).div (continuous_const.mul (hB.max hL))
    intro p
    have hpos := (Uniform05.demandLo_pos i).trans_le p.2.1.property.1
    exact (mul_pos (Uniform05.xi_range i).1
      (hpos.trans_le (le_max_right (p.2.2:ℝ) p.2.1))).ne'
  exact (hV.mul ((continuous_const.mul hp).sub (hp.pow 2))).sub
    (((continuous_const.mul hB).mul hp).mul
      (continuous_const.sub (continuous_const.mul hp)))

theorem product_uniform_modulus (i : Row) {tol : ℝ} (htol : 0 < tol) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ v : Value i, ∀ L K : ProductRoot i,
      ∀ b c : Bid i, |(L:ℝ)-K| < radius → |(b:ℝ)-c| < radius →
        |productPayoff (Uniform05.xi i) v L b-
          productPayoff (Uniform05.xi i) v K c| < tol := by
  obtain ⟨radius,hr,hmod⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous (continuous_productBoxPayoff i)) tol htol
  refine ⟨radius,hr,?_⟩
  intro v L K b c hL hb
  have hd : dist (v,(L,b)) (v,(K,c)) < radius := by
    simp only [Prod.dist_eq,dist_self,Subtype.dist_eq,Real.dist_eq]
    exact max_lt hr (max_lt hL hb)
  simpa only [Real.dist_eq,productBoxPayoff] using hmod hd

theorem own_noise_product_error (i : Row) {tol : ℝ} (htol : 0 < tol) :
    ∃ eps0 : ℝ, 0 < eps0 ∧ ∀ eps : unitInterval, (eps:ℝ) ≤ eps0 →
      ∀ (G : Uniform05.RestrictedLaw i) (p : Value i × unitInterval) (z : unitInterval),
        |productPayoff (Uniform05.xi i) p.1 G.multiplier (noisyBid i (eps,(p,z)))-
          choiceProduct i G p| < tol := by
  obtain ⟨radius,hr,hmod⟩ := product_uniform_modulus i htol
  let eps0 := radius/(2*Uniform05.t i)
  have ht := Uniform05.t_pos i
  have he0 : 0 < eps0 := by unfold eps0; positivity
  refine ⟨eps0,he0,?_⟩
  intro eps heps G p z
  have hd : |(noisyBid i (eps,(p,z)):ℝ)-(baseBid i p:ℝ)| < radius := by
    calc
      _ ≤ (eps:ℝ)*(p.1:ℝ) := physical_base_error i eps p z
      _ ≤ eps0*Uniform05.t i := mul_le_mul heps p.1.property.2
        p.1.property.1 he0.le
      _ = radius/2 := by dsimp [eps0]; field_simp [ht.ne']
      _ < radius := by linarith
  exact hmod p.1 (actualProductRoot i G) (actualProductRoot i G)
    (noisyBid i (eps,(p,z))) (baseBid i p) (by simpa using hr) hd

theorem noisy_uniform_product_menu (i : Row) {tol : ℝ} (htol : 0 < tol) :
    ∃ N0 : ℕ, ∃ eps0 : ℝ, 0 < eps0 ∧
      ∀ N : ℕ, N0 ≤ N → ∀ eps : unitInterval, (eps:ℝ) ≤ eps0 →
        ∀ (pi : Joint i) (p : Value i × unitInterval),
          |expectedUtility i N eps pi p.1 p.2-
            choiceProduct i (restrictedLaw i (eps,pi)) p| < tol := by
  have hquarter : 0 < tol/4 := by linarith
  obtain ⟨N0,hN0⟩ := eventually_atTop.mp (Source.uniform_product_menu i (tol/4) hquarter)
  obtain ⟨eps0,he0,hnoise⟩ := own_noise_product_error i hquarter
  refine ⟨N0,eps0,he0,?_⟩
  intro N hN eps heps pi p
  let G := restrictedLaw i (eps,pi)
  let c := choiceProduct i G p
  have hpoint (z : unitInterval) :
      |rawUtility i N G p.1 (noisyBid i (eps,(p,z)))-c| ≤ tol/2 := by
    calc
      _ ≤ |rawUtility i N G p.1 (noisyBid i (eps,(p,z)))-
        productPayoff (Uniform05.xi i) p.1 G.multiplier (noisyBid i (eps,(p,z)))|+
        |productPayoff (Uniform05.xi i) p.1 G.multiplier (noisyBid i (eps,(p,z)))-c| :=
          abs_sub_le _ _ _
      _ ≤ tol/4+tol/4 := add_le_add
        (hN0 N hN G p.1 (noisyBid i (eps,(p,z))) p.1.property).le
        (hnoise eps heps G p z).le
      _ = tol/2 := by ring
  have hi := integrable_rawUtility_own_noise i N eps pi p.1 p.2
  have hbound : |expectedUtility i N eps pi p.1 p.2-c| ≤ tol/2 := by
    rw [expectedUtility_eq_raw_noise]
    have hconst : (∫_z : unitInterval,c) = c := by simp
    rw [← hconst,← integral_sub hi (integrable_const c)]
    simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using
      norm_integral_le_of_norm_le_const
        (f := fun z : unitInterval => rawUtility i N G p.1 (noisyBid i (eps,(p,z)))-c)
        (C := tol/2)
        (ae_of_all (volume : Measure unitInterval) (fun z => by
          simpa only [Real.norm_eq_abs] using hpoint z))
  exact hbound.trans_lt (by linarith)

def noisyMenuError (i : Row) (N : ℕ) (eps : unitInterval) (pi : Joint i) : ℝ :=
  sSup (range (fun p : Value i × unitInterval =>
    |expectedUtility i N eps pi p.1 p.2-
      choiceProduct i (restrictedLaw i (eps,pi)) p|))

private theorem noisyMenuError_range_bounded (i : Row) (N : ℕ)
    (eps : unitInterval) (pi : Joint i) :
    BddAbove (range (fun p : Value i × unitInterval =>
      |expectedUtility i N eps pi p.1 p.2-
        choiceProduct i (restrictedLaw i (eps,pi)) p|)) := by
  refine ⟨6*Uniform05.t i,?_⟩
  rintro _ ⟨p,rfl⟩
  have hL := (Uniform05.demandLo_pos i).trans
    (restrictedLaw i (eps,pi)).multiplier_guards.1
  have hp := Source.productPayoff_bound i hL p.1.property (baseBid i p).property
  have hu := (expectedUtility_bound i N eps pi p.1 p.2).trans
    (mul_le_mul_of_nonneg_left p.1.property.2 (by norm_num : (0:ℝ)≤3))
  exact (abs_sub _ _).trans (by dsimp [choiceProduct] at *; linarith)

theorem noisyMenuError_bounds (i : Row) (N : ℕ) (eps : unitInterval) (pi : Joint i) :
    0 ≤ noisyMenuError i N eps pi ∧ ∀ p : Value i × unitInterval,
      |expectedUtility i N eps pi p.1 p.2-
        choiceProduct i (restrictedLaw i (eps,pi)) p| ≤ noisyMenuError i N eps pi := by
  have hle (p : Value i × unitInterval) :=
    le_csSup (noisyMenuError_range_bounded i N eps pi) (mem_range_self p)
  refine ⟨?_,hle⟩
  exact (abs_nonneg _).trans (hle (Classical.choice inferInstance))

theorem noisyMenuError_le (i : Row) (N : ℕ) (eps : unitInterval) (pi : Joint i)
    {c : ℝ} (hc : ∀ p : Value i × unitInterval,
      |expectedUtility i N eps pi p.1 p.2-
        choiceProduct i (restrictedLaw i (eps,pi)) p| ≤ c) :
    noisyMenuError i N eps pi ≤ c := by
  apply csSup_le (range_nonempty _)
  rintro _ ⟨p,rfl⟩
  exact hc p

theorem tendsto_noisyMenuError (i : Row) (N : ℕ → ℕ) (eps : ℕ → unitInterval)
    (pi : ℕ → Joint i) (hN : Tendsto N atTop atTop)
    (heps : Tendsto eps atTop (𝓝 0)) :
    Tendsto (fun n => noisyMenuError i (N n) (eps n) (pi n)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro tol htol
  obtain ⟨N0,eps0,he0,hmenu⟩ := noisy_uniform_product_menu i
    (show 0 < tol/2 by linarith)
  have her : Tendsto (fun n => (eps n:ℝ)) atTop (𝓝 0) :=
    continuous_subtype_val.continuousAt.tendsto.comp heps
  filter_upwards [hN.eventually (eventually_ge_atTop N0),
    her.eventually (Iio_mem_nhds he0)] with n hn hen
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (noisyMenuError_bounds i (N n) (eps n) (pi n)).1]
  exact (noisyMenuError_le i (N n) (eps n) (pi n)
    (fun p => (hmenu (N n) hn (eps n) hen.le (pi n) p).le)).trans_lt (by linarith)

theorem product_optimality_of_large_noisy_sequence (i : Row)
    (N : ℕ → ℕ) (eps : ℕ → unitInterval) (pi : ℕ → Joint i) (pi0 : Joint i)
    (hN : Tendsto N atTop atTop) (heps : Tendsto eps atTop (𝓝 0))
    (hpi : Tendsto pi atTop (𝓝 pi0)) (hIC : ∀ n, NoisyIC i (N n) (eps n) (pi n)) :
    ProductOptimal i (restrictedLaw i (0,pi0)) :=
  product_optimality_from_noisy_IC i N eps pi pi0 heps hpi hIC
    (fun n => noisyMenuError i (N n) (eps n) (pi n))
    (fun n => (noisyMenuError_bounds i (N n) (eps n) (pi n)).1)
    (tendsto_noisyMenuError i N eps pi hN heps)
    (fun n => (noisyMenuError_bounds i (N n) (eps n) (pi n)).2)

theorem noisy_multiplier_localization (i : Row) {radius : ℝ} (hr : 0 < radius) :
    ∃ N0 : ℕ, ∃ eps0 : ℝ, 0 < eps0 ∧
      ∀ N : ℕ, N0 ≤ N → ∀ eps : unitInterval, (eps:ℝ) ≤ eps0 →
        ∀ pi : Joint i, NoisyIC i N eps pi →
          |(restrictedLaw i (eps,pi)).multiplier-Uniform05.lambda i| < radius := by
  by_contra hn
  push Not at hn
  have hbad (n : ℕ) := hn n (1/((n:ℝ)+1)) (by positivity)
  choose N hN eps heps pi hIC hfar using hbad
  have hNt : Tendsto N atTop atTop := tendsto_atTop_mono hN tendsto_id
  have hepsr : Tendsto (fun n => (eps n:ℝ)) atTop (𝓝 0) :=
    squeeze_zero (fun n => (eps n).property.1) heps
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))
  have heps0 : Tendsto eps atTop (𝓝 0) := tendsto_subtype_rng.mpr hepsr
  obtain ⟨pi0,phi,hphi,hpi⟩ := CompactSpace.tendsto_subseq pi
  have hNs := hNt.comp hphi.tendsto_atTop
  have hes := heps0.comp hphi.tendsto_atTop
  have hopt := product_optimality_of_large_noisy_sequence i (N ∘ phi) (eps ∘ phi)
    (pi ∘ phi) pi0 hNs hes hpi (fun n => hIC (phi n))
  have hclear := only_source_multiplier_clears i (restrictedLaw i (0,pi0)) hopt
  have hG := (continuous_restrictedLaw i).continuousAt.tendsto.comp (hes.prodMk_nhds hpi)
  have hroot := Uniform05.RestrictedLaw.continuous_multiplier.continuousAt.tendsto.comp hG
  have hdist : Tendsto (fun n =>
      |(restrictedLaw i (eps (phi n),pi (phi n))).multiplier-Uniform05.lambda i|)
      atTop (𝓝 0) := by
    have hd : Tendsto (fun n =>
        (restrictedLaw i (eps (phi n),pi (phi n))).multiplier-Uniform05.lambda i)
        atTop (𝓝 ((restrictedLaw i (0,pi0)).multiplier-Uniform05.lambda i)) :=
      hroot.sub tendsto_const_nhds
    simpa only [hclear,sub_self,abs_zero] using hd.abs
  have hupper := le_of_tendsto_of_tendsto tendsto_const_nhds hdist
    (Eventually.of_forall (fun n => hfar (phi n)))
  exact (not_le_of_gt hr) hupper

end FCAppendix.Affine.UniformFinite
