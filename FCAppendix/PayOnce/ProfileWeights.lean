import FCAppendix.PayOnce.KernelAgreement

namespace FCAppendix.PayOnce.OwnImpact
open Set CommonList
open scoped BigOperators

theorem impactWeight_eq_focalWeight {m n : ℕ} (b : Fin m → ℝ) (L : ℝ) (i : Fin m)
    (hi : kernel n (b i) L ∈ Ioo (0 : ℝ) 1) :
    impactWeight n b (fun j => kernel n (b j) L) i =
      focalWeight n (b i) (kernel n (b i) L)
        (rivalSensitivity n (fun j : Bayes.Rival i => b j.val) L) := by
  classical
  have hden : (∑ j ∈ interiorSet (fun l => kernel n (b l) L),
      sensitivity n (b j) (kernel n (b j) L)) =
      sensitivity n (b i) (kernel n (b i) L) +
        rivalSensitivity n (fun j : Bayes.Rival i => b j.val) L := by
    rw [interiorSet, Finset.sum_filter]
    have hh := Bayes.sum_focal_rivals i (fun j =>
      if 0 < kernel n (b j) L ∧ kernel n (b j) L < 1 then
        sensitivity n (b j) (kernel n (b j) L) else 0)
    simpa only [if_pos (show 0 < kernel n (b i) L ∧ kernel n (b i) L < 1 from hi),
      rivalSensitivity] using hh.symm
  exact congrArg (fun D => sensitivity n (b i) (kernel n (b i) L) / D) hden

theorem sum_focalWeight_le_one {m n : ℕ} (b : Fin m → ℝ) (L : ℝ) :
    ∑ i ∈ interiorSet (fun j => kernel n (b j) L),
      focalWeight n (b i) (kernel n (b i) L)
        (rivalSensitivity n (fun j : Bayes.Rival i => b j.val) L) ≤ 1 := by
  classical
  have he : (∑ i ∈ interiorSet (fun j => kernel n (b j) L),
      focalWeight n (b i) (kernel n (b i) L)
        (rivalSensitivity n (fun j : Bayes.Rival i => b j.val) L)) =
      ∑ i ∈ interiorSet (fun j => kernel n (b j) L), impactWeight n b (fun j => kernel n (b j) L) i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hip : kernel n (b i) L ∈ Ioo (0 : ℝ) 1 := by simpa [interiorSet] using hi
    exact (impactWeight_eq_focalWeight b L i hip).symm
  rw [he]
  exact sum_impactWeight_le_one n b _

theorem weight_eq_impactWeight_of_derivative {m n c : ℕ} (hn : 2 ≤ n)
    (b : Fin m → ℝ) (hb : ∀ i, 0 < b i) {L : ℝ} (hL : 0 < L)
    (hcap : ∑ j, kernel n (b j) L = c) (i : Fin m)
    (hi : kernel n (b i) L ∈ Ioo (0 : ℝ) 1)
    (hclip0 : ∀ j, b j ≠ L) (hclip1 : ∀ j, b j ≠ (n : ℝ)*L)
    (hc : c ≤ Fintype.card (Bayes.Rival i)+1) (weight : ℝ)
    (hweight : b i * deriv (fun x => success n
      (AnalyticalKernel.allocation n c hn hc (fun j : Bayes.Rival i => b j.val) x)) (b i) =
        RareSuccessSlope.weightedSlope n (kernel n (b i) L) weight) :
    weight = impactWeight n b (fun j => kernel n (b j) L) i := by
  have hcap' := (Bayes.sum_focal_rivals i (fun j => kernel n (b j) L)).trans hcap
  have hd := focal_success_derivative_ownImpact hn (fun j : Bayes.Rival i => b j.val)
    (fun j => hb j.val) _ (hb i) hL hcap' hi
    (fun j => hclip0 j.val) (fun j => hclip1 j.val)
    (fun x hx => AnalyticalKernel.allocation_root hn hc _ (fun j => hb j.val) hx)
  rw [RareSuccessSlope.weightedSlope, if_pos (show 0 < kernel n (b i) L ∧ kernel n (b i) L < 1 from hi)] at hweight
  change b i * _ = RareSuccessSlope.phi n (kernel n (b i) L) * _ at hd
  have hφ := AnalyticalKernel.phi_pos_interior hn hi
  rw [impactWeight_eq_focalWeight b L i hi]
  nlinarith [hweight, hd]

end FCAppendix.PayOnce.OwnImpact
