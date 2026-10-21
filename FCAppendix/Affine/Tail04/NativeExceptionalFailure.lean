import FCAppendix.Affine.Hybrid.Native02.ExceptionalClipped
import FCAppendix.Probability.Bounds

noncomputable section
namespace FCAppendix.Affine.Tail04.NativeExceptionalFailure
open MeasureTheory Set Filter Topology
open Hybrid Hybrid.Native02
open scoped BigOperators

lemma failure_square_lipschitz {p q : ℝ} (hp : p∈Icc (0:ℝ) 1)
    (hq : q∈Icc (0:ℝ) 1) :
    |(1-q)^2-(1-p)^2|≤2*|q-p| := by
  have he : (1-q)^2-(1-p)^2=-(q-p)*(2-q-p) := by ring
  have hf : |2-q-p|≤2 := by rw [abs_le];constructor <;> linarith [hp.1,hp.2,hq.1,hq.2]
  rw [he,abs_mul,abs_neg]
  have hh := mul_le_mul_of_nonneg_left hf (abs_nonneg (q-p))
  nlinarith only [hh]

lemma threshold_failure_error {xi d b price lam q : ℝ}
    (hxi : 0<xi) (hxi1 : xi<1) (hd : 0<d) (hdb : d≤b)
    (ht : EqualCapacity.ScalarThreshold xi b price q) :
    |(1-q)^2-(1-EqualCapacity.demand xi b lam)^2|≤
      (2/(xi*d))*|price-lam| := by
  have hb : 0<b := hd.trans_le hdb
  have hq : q∈Icc (0:ℝ) 1 := ⟨ht.1,ht.2.1⟩
  have he := failure_square_lipschitz (EqualCapacity.demand_bounds xi b lam) hq
  have hdiff : |q-EqualCapacity.demand xi b lam|≤|price-lam|/(xi*d) := by
    rw [scalarThreshold_eq_demand hxi hxi1 hb ht]
    exact (demand_price_lipschitz hxi hb price lam).trans
      (div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos hxi hd)
        (mul_le_mul_of_nonneg_left hdb hxi.le))
  have hh := he.trans (mul_le_mul_of_nonneg_left hdiff (by norm_num : (0:ℝ)≤2))
  exact hh.trans_eq (by ring)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem sourceOwners_failure_error
    (G : Measure ℝ) [IsProbabilityMeasure G] {xi d L U h0 b : ℝ}
    (hxi : 0<xi) (hxi1 : xi<1) (hd : 0<d) (hdb : d≤b)
    (hL : 0<L) (hLU : L≤U) (hbox : ∀ᵐx ∂G,x∈Icc L U) (hh0 : |h0|≤1)
    (K₁ K₂ r : ℕ) (hN : 2≤Fintype.card ι) (hK : K₁+K₂<Fintype.card ι)
    (q : (ι→ℝ)→(Finset ι×Finset ι)→ℝ)
    (hqmeas : ∀AB,Measurable (fun x=>q x AB))
    (hq : ∀x AB,q x AB∈Icc (0:ℝ) 1)
    (ht : ∀ᵐx ∂Measure.pi (fun _ : ι=>G),∀AB,
      (sourceOwnersLaw x K₁ K₂).mass AB≠0→
      EqualCapacity.ScalarThreshold xi b
        (clippedPriceFromRivals xi x (Finset.univ \ (AB.1∪AB.2)) r (q x AB)) (q x AB)) :
    let n:=Fintype.card ι-(K₁+K₂)
    let err:=U*|finiteReceiptFactor xi n r-h0|+
      U^2*(2*((1/L)/Real.sqrt (n:ℝ)))+xi*U/(n:ℝ)
    |(∫x : ι→ℝ,(sourceOwnersLaw x K₁ K₂).expect (fun AB=>(1-q x AB)^2)
      ∂Measure.pi (fun _ : ι=>G))-
      (1-EqualCapacity.demand xi b (h0/reciprocalMean G))^2|≤(2/(xi*d))*err := by
  let P:=Measure.pi (fun _ : ι=>G)
  let lam:=h0/reciprocalMean G
  let c:=(1-EqualCapacity.demand xi b lam)^2
  let C:=2/(xi*d)
  let error : (ι→ℝ)→ℝ:=fun x=>(sourceOwnersLaw x K₁ K₂).expect (fun AB=>
    |clippedPriceFromRivals xi x (Finset.univ \ (AB.1∪AB.2)) r (q x AB)-lam|)
  have hC : 0≤C := by dsimp [C];positivity
  have herror : Integrable error P :=
    integrable_sourceOwners_expect G K₁ K₂ _ (fun AB=>
      ((integrable_clippedPriceFromRivals G hxi hL hLU hbox _ r
        (fun x=>q x AB) (hqmeas AB) (fun x=>hq x AB)).sub (integrable_const _)).abs)
  have hf (AB : Finset ι×Finset ι) : Integrable (fun x=>(1-q x AB)^2) P := by
    apply Integrable.of_bound ((measurable_const.sub (hqmeas AB)).pow_const 2).aestronglyMeasurable 1
    exact Eventually.of_forall (fun x=>by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      change (1-q x AB)^2≤1
      nlinarith [(hq x AB).1,(hq x AB).2])
  have hfi : Integrable (fun x=>(sourceOwnersLaw x K₁ K₂).expect (fun AB=>(1-q x AB)^2)) P :=
    integrable_sourceOwners_expect G K₁ K₂ _ hf
  have hdi : Integrable (fun x=>(sourceOwnersLaw x K₁ K₂).expect (fun AB=>(1-q x AB)^2-c)) P :=
    integrable_sourceOwners_expect G K₁ K₂ _ (fun AB=>(hf AB).sub (integrable_const c))
  have hpoint : ∀ᵐx ∂P,
      |(sourceOwnersLaw x K₁ K₂).expect (fun AB=>(1-q x AB)^2-c)|≤C*error x := by
    filter_upwards [ht] with x hx
    calc
      _ ≤ (sourceOwnersLaw x K₁ K₂).expect (fun AB=>|(1-q x AB)^2-c|) :=
        (sourceOwnersLaw x K₁ K₂).abs_expect_le _
      _ ≤ (sourceOwnersLaw x K₁ K₂).expect (fun AB=>C*
          |clippedPriceFromRivals xi x (Finset.univ \ (AB.1∪AB.2)) r (q x AB)-lam|) :=
        expect_le_expect_on_support _ (fun AB hAB=>
          threshold_failure_error hxi hxi1 hd hdb (hx AB hAB))
      _ = _ := FiniteLaw.expect_const_mul _ _ _
  have hi0 : |∫x,(sourceOwnersLaw x K₁ K₂).expect (fun AB=>(1-q x AB)^2-c) ∂P|≤
      ∫x,|(sourceOwnersLaw x K₁ K₂).expect (fun AB=>(1-q x AB)^2-c)| ∂P :=
    abs_integral_le_integral_abs
  have hi := hi0.trans (integral_mono_ae hdi.abs (herror.const_mul C) hpoint)
  have hc : (∫x,(sourceOwnersLaw x K₁ K₂).expect (fun AB=>(1-q x AB)^2-c) ∂P)=
      (∫x,(sourceOwnersLaw x K₁ K₂).expect (fun AB=>(1-q x AB)^2) ∂P)-c := by
    simp only [FiniteLaw.expect_sub,FiniteLaw.expect_const]
    rw [integral_sub hfi (integrable_const c)]
    simp
  rw [hc,integral_const_mul] at hi
  exact hi.trans (mul_le_mul_of_nonneg_left
    (sourceOwners_clippedPrice_L1 G hxi hL hLU hbox hh0 K₁ K₂ r hN hK q hqmeas hq) hC)

theorem primitive_excluded_owner_failure
    (G : Measure ℝ) [IsProbabilityMeasure G] {xi d L U h0 b : ℝ}
    (hxi : 0<xi) (hxi1 : xi<1) (hd : 0<d) (hdb : d≤b)
    (hL : 0<L) (hLU : L≤U) (hbox : ∀ᵐx ∂G,x∈Icc L U) (hh0 : |h0|≤1)
    (K₁ K₂ r : ℕ) (hN : 2≤Fintype.card ι) (hK : K₁+K₂<Fintype.card ι)
    (hguard : ClippedCountGuard xi L U (Fintype.card ι-(K₁+K₂)+1) r) :
    let n:=Fintype.card ι-(K₁+K₂)
    let err:=U*|finiteReceiptFactor xi n r-h0|+
      U^2*(2*((1/L)/Real.sqrt (n:ℝ)))+xi*U/(n:ℝ)
    |(∫x : ι→ℝ,(sourceOwnersLaw x K₁ K₂).expect
      (fun AB=>(1-canonicalExceptionalQ xi r b x AB)^2) ∂Measure.pi (fun _ : ι=>G))-
      (1-EqualCapacity.demand xi b (h0/reciprocalMean G))^2|≤(2/(xi*d))*err := by
  apply sourceOwners_failure_error G hxi hxi1 hd hdb hL hLU hbox hh0 K₁ K₂ r hN hK
    (canonicalExceptionalQ xi r b) (measurable_canonicalExceptionalQ hxi hxi1 r b)
    (fun x AB=>canonicalExceptionalQ_bounds hxi hxi1 r b x AB)
  filter_upwards [ae_iid_rival_box G hbox] with x hx
  intro AB hAB
  obtain ⟨h₁,h₂,hdis⟩:=sourceOwnersLaw_support x K₁ K₂ hN hK.le AB.1 AB.2 hAB
  have hcard : (Finset.univ \ (AB.1∪AB.2)).card=Fintype.card ι-(K₁+K₂) := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,
      Finset.card_union_of_disjoint hdis,h₁,h₂]
  exact canonicalExceptionalQ_threshold hxi hxi1 hL hLU (hd.trans_le hdb) x hx
    AB.1 AB.2 hdis r (by rw [hcard];exact hguard)

end FCAppendix.Affine.Tail04.NativeExceptionalFailure
