import FCAppendix.Game.PosteriorReceipts
import FCAppendix.Game.PosteriorFeasible
import FCAppendix.Finite.ReceiptBoundsAE

noncomputable section
namespace FCAppendix.Affine.Tail04.PosteriorReceiptNormalization
open MeasureTheory ProbabilityTheory Set Filter Classical Game Bayes

variable {m n c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
variable (Γ : FiniteGame m n c Seed)
    (κ : Fin n → Kernel (LocalList m) (UserProfile m n))
    [∀ j,IsMarkovKernel (κ j)]

def background (j : Fin n) (L : LocalList m) : Measure (Background m n Seed) :=
  (κ j L).prod (Measure.pi (fun _ : Fin n => Γ.seedLaw))

instance (j : Fin n) (L : LocalList m) : IsProbabilityMeasure (background Γ κ j L) := by
  unfold background
  infer_instance

def countBelief (j : Fin n) (L : LocalList m) (i : Fin m) : FiniteLaw (Fin n) :=
  FiniteLaw.ofMeasure (background Γ κ j L) (otherInclusionCount Γ j i)
    (measurable_otherInclusionCount Γ j i)

def factor (j : Fin n) (L : LocalList m) (i : Fin m) : ℝ :=
  (countBelief Γ κ j L i).expect (fun r => Γ.A.receiptRatio (r.val+1))

def receipts (j : Fin n) (L : LocalList m) : Fin m → ℝ :=
  beliefReceipts Γ.A (countBelief Γ κ j L) L

lemma receipts_entry (j : Fin n) (L : LocalList m) (i : Fin m) :
    receipts Γ κ j L i=entryBid (L i)*factor Γ κ j L i := by
  cases he : L i with
  | none => simp [receipts,beliefReceipts,he,entryBid]
  | some b =>
    simp only [receipts,beliefReceipts,he,entryBid,factor]
    exact conditionalReceipt_eq_mul_ratio_expect _ _ _

lemma measurable_factor (j : Fin n) (i : Fin m) :
    Measurable (fun L => factor Γ κ j L i) := by
  let f : Background m n Seed → ℝ := fun ω =>
    Γ.A.receiptRatio ((otherInclusionCount Γ j i ω).val+1)
  have hf : Measurable f := (measurable_of_countable
    (fun r : Fin n => Γ.A.receiptRatio (r.val+1))).comp (measurable_otherInclusionCount Γ j i)
  have hb : ∀ ω,‖f ω‖≤1 := by
    intro ω
    have h := receiptRatio_unit Γ.A (otherInclusionCount Γ j i ω)
    simpa only [f,Real.norm_eq_abs,abs_of_nonneg h.1] using h.2
  have he (L : LocalList m) : factor Γ κ j L i=
      ∫ d,∫ s,f (d,s) ∂Measure.pi (fun _ : Fin n => Γ.seedLaw) ∂κ j L := by
    rw [factor,countBelief,FiniteLaw.expect_ofMeasure]
    exact integral_prod f (Integrable.of_bound hf.aestronglyMeasurable 1 (ae_of_all _ hb))
  have hm : Measurable (fun d : UserProfile m n =>
      ∫ s,f (d,s) ∂Measure.pi (fun _ : Fin n => Γ.seedLaw)) :=
    hf.stronglyMeasurable.integral_prod_right'.measurable
  have hmk : Measurable (fun z : LocalList m×UserProfile m n =>
      ∫ s,f (z.2,s) ∂Measure.pi (fun _ : Fin n => Γ.seedLaw)) := hm.comp measurable_snd
  simp_rw [he]
  exact hmk.stronglyMeasurable.integral_kernel_prod_right'.measurable

lemma measurable_receipts (j : Fin n) : Measurable (receipts Γ κ j) :=
  measurable_pi_iff.mpr (fun i => by
    simp_rw [receipts_entry]
    exact (measurable_entryBid.comp (measurable_pi_apply i)).mul (measurable_factor Γ κ j i))

lemma receipts_posterior (B : PosteriorSystem Γ) (j : Fin n) (L : LocalList m) :
    receipts Γ B.posterior j L=beliefReceipts Γ.A (posteriorCountBelief Γ B j L) L := rfl

variable (B : PosteriorSystem Γ)

def good (j : Fin n) : Set (LocalList m) :=
  {L | receipts Γ B.posterior j L=receipts Γ κ j L}

lemma measurableSet_good (j : Fin n) : MeasurableSet (good Γ κ B j) := by
  have he : good Γ κ B j=⋂ i : Fin m,
      {L | receipts Γ B.posterior j L i=receipts Γ κ j L i} := by
    ext L
    simp [good,funext_iff]
  rw [he]
  exact MeasurableSet.iInter (fun i => measurableSet_eq_fun
    ((measurable_pi_apply i).comp (measurable_receipts Γ B.posterior j))
    ((measurable_pi_apply i).comp (measurable_receipts Γ κ j)))

def normalizedKernel (j : Fin n) : Kernel (LocalList m) (UserProfile m n) :=
  Kernel.piecewise (measurableSet_good Γ κ B j) (B.posterior j) (κ j)

instance (j : Fin n) : IsMarkovKernel (normalizedKernel Γ κ B j) := by
  unfold normalizedKernel
  infer_instance

variable (hfull : ∀ j,∀ᵐ L ∂observedListLaw Γ j,
    receipts Γ B.posterior j L=receipts Γ κ j L)
    (hfeasible : ∀ j L,FeasibleObservedList j L →
      ∀ᵐ d ∂κ j L,observe (drawsRealization d) j=L)

def normalized : PosteriorSystem Γ where
  posterior := normalizedKernel Γ κ B
  markov j := inferInstance
  on_path j := by
    have he : normalizedKernel Γ κ B j=ᵐ[observedListLaw Γ j] B.posterior j := by
      filter_upwards [hfull j] with L hL
      simp only [normalizedKernel,Kernel.piecewise_apply,if_pos (show L∈good Γ κ B j from hL)]
    exact (B.on_path j).trans (Measure.compProd_congr he).symm
  feasible j L hL := by
    by_cases hg : L∈good Γ κ B j
    · simpa only [normalizedKernel,Kernel.piecewise_apply,if_pos hg] using B.feasible j L hL
    · simpa only [normalizedKernel,Kernel.piecewise_apply,if_neg hg] using hfeasible j L hL

theorem normalized_receipts (j : Fin n) (L : LocalList m) :
    beliefReceipts Γ.A (posteriorCountBelief Γ (normalized Γ κ B hfull hfeasible) j L) L=
      receipts Γ κ j L := by
  change receipts Γ (normalized Γ κ B hfull hfeasible).posterior j L=_
  by_cases hg : L∈good Γ κ B j
  · have he : normalizedKernel Γ κ B j L=B.posterior j L := by
      simp only [normalizedKernel,Kernel.piecewise_apply,if_pos hg]
    have hr : receipts Γ (normalizedKernel Γ κ B) j L=receipts Γ B.posterior j L := by
      unfold receipts countBelief background
      simp only [he]
    exact hr.trans hg
  · have he : normalizedKernel Γ κ B j L=κ j L := by
      simp only [normalizedKernel,Kernel.piecewise_apply,if_neg hg]
    unfold receipts countBelief background
    simp only [normalized,he]

theorem normalized_optimal
    (hopt : ∀ j L,FeasibleObservedList j L → ∀ u,
      Finite.Optimal c (receipts Γ κ j L) ((Γ.policy j L u).val)) :
    PosteriorProposerOptimalAE Γ (normalized Γ κ B hfull hfeasible) := by
  intro j L hL
  rw [normalized_receipts]
  exact ae_of_all _ (hopt j L hL)

end FCAppendix.Affine.Tail04.PosteriorReceiptNormalization
