import FCAppendix.Affine.Uniform07Finishing.Native.GuardedSeedErasure
import FCAppendix.Affine.Hybrid.PrivateSeedPayoff
import FCAppendix.Finite.IdentitySymmetry

set_option maxHeartbeats 600000

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing
open MeasureTheory ProbabilityTheory Game Bayes Set Classical
open FCAppendix.Affine LowBody

variable {m : ℕ}

def twoCountPolynomial (q : Fin 3 → ℝ) (p₀ p₁ : ℝ) : ℝ :=
  q 0+(q 1-q 0)*(p₀+p₁)+(q 2-2*q 1+q 0)*(p₀*p₁)

theorem private_pair_count_moment
    (f g : unitInterval → Finset (Fin m)) (hf : Measurable f) (hg : Measurable g)
    (i : Fin m) (q : Fin 3 → ℝ) :
    (∫s : Fin 2 → unitInterval, q (focalCopy (f (s 0),g (s 1)) i)
      ∂Measure.pi (fun _ : Fin 2 => (volume : Measure unitInterval))) =
      twoCountPolynomial q
        (∫s : unitInterval, if i ∈ f s then (1 : ℝ) else 0)
        (∫s : unitInterval, if i ∈ g s then (1 : ℝ) else 0) := by
  let b : Fin m → ℝ := fun _ => q 1-q 2
  let v := 2*q 1-q 2-q 0
  have he (P : Finset (Fin m) × Finset (Fin m)) :
      q (focalCopy P i) = q 0+purePayoff 1 v b P i := by
    unfold purePayoff
    generalize focalCopy P i = r
    fin_cases r <;> norm_num [v,b,Fin.ext_iff] <;> ring_nf
    exact congrArg q (Fin.ext rfl)
  have hcopy : Measurable (fun s : Fin 2 → unitInterval => focalCopy (f (s 0),g (s 1)) i) :=
    (measurable_of_countable (fun P : Finset (Fin m) × Finset (Fin m) => focalCopy P i)).comp
      ((hf.comp (measurable_pi_apply 0)).prodMk (hg.comp (measurable_pi_apply 1)))
  have hi : Integrable (fun s : Fin 2 → unitInterval =>
      purePayoff 1 v b (f (s 0),g (s 1)) i)
      (Measure.pi (fun _ : Fin 2 => (volume : Measure unitInterval))) := by
    let Q : Fin 3 → ℝ := fun r => if r=2 then v-2*b i else if r=1 then v-b i else 0
    simpa only [Q, purePayoff, mul_one] using
      (CountLaw.integrable_comp _ _ hcopy Q)
  have hpay := Hybrid.NativeContinuation.private_pair_expected_payoff
    0 v b i f g hf hg
  simp only [sub_zero] at hpay
  simp_rw [he]
  rw [integral_add (integrable_const _) hi, integral_const, probReal_univ,
    smul_eq_mul, one_mul, hpay]
  simp only [twoCountPolynomial, v,b]
  ring

theorem private_pair_count_moment_eq_of_marginals
    (f₀ f₁ g₀ g₁ : unitInterval → Finset (Fin m))
    (hf₀ : Measurable f₀) (hf₁ : Measurable f₁) (hg₀ : Measurable g₀) (hg₁ : Measurable g₁)
    (i l : Fin m)
    (h₀ : (∫s : unitInterval, if i ∈ f₀ s then (1 : ℝ) else 0) =
      ∫s : unitInterval, if l ∈ g₀ s then (1 : ℝ) else 0)
    (h₁ : (∫s : unitInterval, if i ∈ f₁ s then (1 : ℝ) else 0) =
      ∫s : unitInterval, if l ∈ g₁ s then (1 : ℝ) else 0) (q : Fin 3 → ℝ) :
    (∫s : Fin 2 → unitInterval, q (focalCopy (f₀ (s 0),f₁ (s 1)) i)
      ∂Measure.pi (fun _ : Fin 2 => (volume : Measure unitInterval))) =
      ∫s : Fin 2 → unitInterval, q (focalCopy (g₀ (s 0),g₁ (s 1)) l)
        ∂Measure.pi (fun _ : Fin 2 => (volume : Measure unitInterval)) := by
  rw [private_pair_count_moment f₀ f₁ hf₀ hf₁, private_pair_count_moment g₀ g₁ hg₀ hg₁,
    h₀,h₁]

namespace Weighted
open StrictNative
variable [Nonempty (Fin m)]

local instance : DiscreteMeasurableSpace (Option (Finset (Fin m))) :=
  ⟨fun s => by
    change MeasurableSet ((some : Finset (Fin m) → Option (Finset (Fin m))) ⁻¹' s)
    exact MeasurableSet.of_discrete⟩

def privateCountMoment (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ)
    (X : ClassifiedContext m) (E : Option (Finset (Fin m))) (i : Fin m)
    (q : Fin 3 → ℝ) : ℝ :=
  ∫s : Fin 2 → unitInterval,
    q (focalCopy (select ξ hξ hξ1 c (fun _ => E) 0 X (s 0),
      select ξ hξ hξ1 c (fun _ => E) 1 X (s 1)) i)
        ∂Measure.pi (fun _ : Fin 2 => (volume : Measure unitInterval))

theorem privateCountMoment_eq_acceptance (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ)
    (X : ClassifiedContext m) (E : Option (Finset (Fin m))) (i : Fin m) (q : Fin 3 → ℝ) :
    privateCountMoment ξ hξ hξ1 c X E i q =
      twoCountPolynomial q
        (acceptance ξ hξ hξ1 c (fun _ => E) 0 X i)
        (acceptance ξ hξ hξ1 c (fun _ => E) 1 X i) := by
  exact private_pair_count_moment _ _
    ((measurable_select ξ hξ hξ1 c (fun _ => E) measurable_const 0).comp
      (measurable_const.prodMk measurable_id))
    ((measurable_select ξ hξ hξ1 c (fun _ => E) measurable_const 1).comp
      (measurable_const.prodMk measurable_id)) i q

theorem privateCountMoment_equal (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ)
    (X : ClassifiedContext m) (E : Option (Finset (Fin m)))
    (he : budget c 0 X = budget c 1 X) (i : Fin m) (q : Fin 3 → ℝ) :
    privateCountMoment ξ hξ hξ1 c X E i q =
      twoCountPolynomial q
        (EqualCapacity.positiveMarginal ξ (budget c 0 X) (Existence.PayOnceBounded.listBids X.1) i)
        (EqualCapacity.positiveMarginal ξ (budget c 0 X) (Existence.PayOnceBounded.listBids X.1) i) := by
  rw [privateCountMoment_eq_acceptance, acceptance_equal _ _ _ _ _ 0 X he,
    acceptance_equal _ _ _ _ _ 1 X he]

theorem privateCountMoment_weighted (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ)
    (X : ClassifiedContext m) (E : Finset (Fin m))
    (he : budget c 0 X ≠ budget c 1 X)
    (hE : ValidExclusive ξ X.1 (budget c 0 X) (budget c 1 X) E)
    (i : Fin m) (q : Fin 3 → ℝ) :
    privateCountMoment ξ hξ hξ1 c X (some E) i q =
      let p := EqualCapacity.positiveMarginal ξ (commonBudget c X)
        (Existence.PayOnceBounded.listBids (remainder X.1 E)) i
      twoCountPolynomial q
        (if (0 : Fin 2) = larger c X ∧ i ∈ E then 1 else p)
        (if (1 : Fin 2) = larger c X ∧ i ∈ E then 1 else p) := by
  have hu : usable ξ c (fun _ : ClassifiedContext m => some E) X :=
    ⟨Option.some_ne_none _, by simpa only [candidate, Option.getD_some] using hE⟩
  rw [privateCountMoment_eq_acceptance,
    acceptance_weighted _ _ _ _ _ 0 X he hu,
    acceptance_weighted _ _ _ _ _ 1 X he hu]
  rfl

theorem privateCountMoment_none (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ)
    (X : ClassifiedContext m) (he : budget c 0 X ≠ budget c 1 X)
    (i : Fin m) (q : Fin 3 → ℝ) :
    privateCountMoment ξ hξ hξ1 c X none i q = q (focalCopy (purePair ξ c X) i) := by
  have hn : ¬ usable ξ c (fun _ : ClassifiedContext m => none) X := fun h => h.1 rfl
  simp only [privateCountMoment, select, if_neg he, if_neg hn, if_true,
    if_neg (by decide : (1 : Fin 2) ≠ 0), integral_const, probReal_univ, smul_eq_mul, one_mul]

theorem privateCountMoment_at_actual_plan
    (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1) (c : ℕ)
    (plan : ClassifiedContext m → Option (Finset (Fin m)))
    (X : ClassifiedContext m) (i : Fin m) (q : Fin 3 → ℝ) :
    (∫s : Fin 2 → unitInterval,
      q (focalCopy (select ξ hξ hξ1 c plan 0 X (s 0),
        select ξ hξ hξ1 c plan 1 X (s 1)) i)
        ∂Measure.pi (fun _ : Fin 2 => (volume : Measure unitInterval))) =
      privateCountMoment ξ hξ hξ1 c X (plan X) i q := by
  rfl

theorem measurable_privateCountMoment (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (i : Fin m) (q : Fin 3 → ℝ) :
    Measurable (fun p : ClassifiedContext m × Option (Finset (Fin m)) =>
      privateCountMoment ξ hξ hξ1 c p.1 p.2 i q) := by
  have hE (E : Option (Finset (Fin m))) : Measurable
      (fun X : ClassifiedContext m => privateCountMoment ξ hξ hξ1 c X E i q) := by
    let F : ClassifiedContext m × (Fin 2 → unitInterval) → ℝ := fun x =>
      q (focalCopy (select ξ hξ hξ1 c (fun _ => E) 0 x.1 (x.2 0),
        select ξ hξ hξ1 c (fun _ => E) 1 x.1 (x.2 1)) i)
    have hinput (j : Fin 2) : Measurable (fun x : ClassifiedContext m × (Fin 2 → unitInterval) =>
        (x.1,x.2 j)) := measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd)
    have hselect (j : Fin 2) : Measurable (fun x : ClassifiedContext m × (Fin 2 → unitInterval) =>
        select ξ hξ hξ1 c (fun _ => E) j x.1 (x.2 j)) := by
      simpa only [Function.comp_def,Function.uncurry] using
        (measurable_select ξ hξ hξ1 c (fun _ => E) measurable_const j).comp (hinput j)
    have hpair : Measurable (fun x : ClassifiedContext m × (Fin 2 → unitInterval) =>
        (select ξ hξ hξ1 c (fun _ => E) 0 x.1 (x.2 0),
          select ξ hξ hξ1 c (fun _ => E) 1 x.1 (x.2 1))) := (hselect 0).prodMk (hselect 1)
    have hF : Measurable F := by
      convert! (measurable_of_countable (fun P : Finset (Fin m) × Finset (Fin m) =>
        q (focalCopy P i))).comp hpair using 1
    convert! (hF.stronglyMeasurable.integral_prod_right'
      (ν := Measure.pi (fun _ : Fin 2 => (volume : Measure unitInterval)))).measurable using 1
  have hm : Measurable (fun p : Option (Finset (Fin m)) × ClassifiedContext m =>
      privateCountMoment ξ hξ hξ1 c p.2 p.1 i q) :=
    measurable_from_prod_countable_right hE
  convert! hm.comp (measurable_snd.prodMk measurable_fst) using 1

theorem abs_privateCountMoment_le (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (c : ℕ) (X : ClassifiedContext m) (E : Option (Finset (Fin m)))
    (i : Fin m) (q : Fin 3 → ℝ) :
    |privateCountMoment ξ hξ hξ1 c X E i q| ≤ ∑r : Fin 3, |q r| := by
  have hq (r : Fin 3) : |q r| ≤ ∑l : Fin 3, |q l| :=
    Finset.single_le_sum (fun l _ => abs_nonneg (q l)) (Finset.mem_univ r)
  have hb : ∀ᵐs : Fin 2 → unitInterval
      ∂Measure.pi (fun _ : Fin 2 => (volume : Measure unitInterval)),
      ‖q (focalCopy (select ξ hξ hξ1 c (fun _ => E) 0 X (s 0),
        select ξ hξ hξ1 c (fun _ => E) 1 X (s 1)) i)‖ ≤ ∑r : Fin 3, |q r| :=
    ae_of_all _ (fun s => by simpa only [Real.norm_eq_abs] using hq _)
  simpa only [privateCountMoment, Real.norm_eq_abs, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const hb

end Weighted
end FCAppendix.Affine.Uniform07Finishing
