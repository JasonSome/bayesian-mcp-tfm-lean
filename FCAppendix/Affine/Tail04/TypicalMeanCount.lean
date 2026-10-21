import FCAppendix.Affine.Tail04.TypicalCountLaws
import FCAppendix.Affine.Tail04.UnusedBidPriceTest
import FCAppendix.Affine.Tail04.IntegerOwnerBalance

noncomputable section
namespace FCAppendix.Affine.Tail04
open Set
open WeightedFlagBound
open scoped BigOperators
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]

def probabilityClip (x : ℝ) : ℝ := min 1 (max 0 x)

theorem probabilityClip_bounds (x : ℝ) : 0 ≤ probabilityClip x ∧ probabilityClip x ≤ 1 :=
  ⟨le_min (by norm_num) (le_max_left _ _),min_le_left _ _⟩

theorem probabilityClip_eq {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : probabilityClip x=x := by
  rw [probabilityClip,max_eq_right hx.1,min_eq_right hx.2]

theorem continuous_probabilityClip : Continuous probabilityClip :=
  continuous_const.min (continuous_const.max continuous_id)

def rawMeanMarginal (xi : ℝ) (c ell : ℕ) (privateMean : ℝ)
    (M : ℕ) (W bi : ℝ) : ℝ :=
  (1-(((M:ℝ)-xi*((c:ℝ)-privateMean-ell))/W)/bi)/xi

def meanMarginal (xi : ℝ) (c ell : ℕ) (privateMean : ℝ)
    (M : ℕ) (W bi : ℝ) : ℝ :=
  probabilityClip (rawMeanMarginal xi c ell privateMean M W bi)

def meanCountLaw (xi : ℝ) (c ell0 ell1 : ℕ) (privateMean0 privateMean1 : ℝ)
    (M : ℕ) (W bi : ℝ) : CountLaw 2 :=
  twoCoinCountLaw
    (meanMarginal xi c ell0 privateMean0 M W bi)
    (meanMarginal xi c ell1 privateMean1 M W bi)
    (probabilityClip_bounds _).1 (probabilityClip_bounds _).2
    (probabilityClip_bounds _).1 (probabilityClip_bounds _).2

theorem privateTypicalMixture_marginal_mean (mu : FiniteLaw Ω)
    {xi : ℝ} (hxi : 0 < xi) (c ell : ℕ) (privateMean : ℝ)
    (fixed : Ω → Finset ι) (I : Finset ι) (b : ι → ℝ)
    (hdis : ∀ omega, Disjoint (fixed omega) I)
    (hfixed : ∀ omega, (fixed omega).card ≤ c)
    (hW : 0 < mixedReciprocalSum I b) (hb : ∀ i ∈ I, 0 < b i)
    (hlo : ∀ omega i, i ∈ I →
      (1-xi)*b i ≤ realizedMixedMultiplier xi c (fixed omega) I b)
    (hhi : ∀ omega i, i ∈ I →
      realizedMixedMultiplier xi c (fixed omega) I b ≤ b i)
    (hmean : mu.expect (fun omega => ((fixed omega).card:ℝ))=privateMean+ell)
    (i : ι) (hi : i ∈ I) :
    (privateTypicalMixture mu xi c fixed I b).prob (fun S => i ∈ S) =
      rawMeanMarginal xi c ell privateMean I.card (mixedReciprocalSum I b) (b i) := by
  have hreceipt := privateTypicalMixture_mixed_receipt mu hxi c fixed I b
    hdis hfixed hW hb hlo hhi i hi
  have hmeanLambda := expected_realizedMixedMultiplier mu xi c fixed I b hfixed
  rw [hmean] at hmeanLambda
  have hprice : mu.expect (fun omega => realizedMixedMultiplier xi c (fixed omega) I b) =
      meanMixedPrice xi c ell privateMean I b := by
    rw [hmeanLambda]
    unfold meanMixedPrice
    congr 1
    ring
  rw [hprice] at hreceipt
  unfold receiptAgainstSelection at hreceipt
  rw [FiniteLaw.expect_const_mul,FiniteLaw.expect_sub,FiniteLaw.expect_const,
    FiniteLaw.expect_const_mul,← FiniteLaw.prob_eq_expect] at hreceipt
  unfold rawMeanMarginal
  change _ = (1-meanMixedPrice xi c ell privateMean I b/b i)/xi
  field_simp [hxi.ne',(hb i hi).ne']
  nlinarith only [hreceipt]

theorem privateTypicalMixture_marginal_mean_clipped (mu : FiniteLaw Ω)
    {xi : ℝ} (hxi : 0 < xi) (c ell : ℕ) (privateMean : ℝ)
    (fixed : Ω → Finset ι) (I : Finset ι) (b : ι → ℝ)
    (hdis : ∀ omega, Disjoint (fixed omega) I)
    (hfixed : ∀ omega, (fixed omega).card ≤ c)
    (hW : 0 < mixedReciprocalSum I b) (hb : ∀ i ∈ I, 0 < b i)
    (hlo : ∀ omega i, i ∈ I →
      (1-xi)*b i ≤ realizedMixedMultiplier xi c (fixed omega) I b)
    (hhi : ∀ omega i, i ∈ I →
      realizedMixedMultiplier xi c (fixed omega) I b ≤ b i)
    (hmean : mu.expect (fun omega => ((fixed omega).card:ℝ))=privateMean+ell)
    (i : ι) (hi : i ∈ I) :
    (privateTypicalMixture mu xi c fixed I b).prob (fun S => i ∈ S) =
      meanMarginal xi c ell privateMean I.card (mixedReciprocalSum I b) (b i) := by
  have he := privateTypicalMixture_marginal_mean mu hxi c ell privateMean fixed I b
    hdis hfixed hW hb hlo hhi hmean i hi
  unfold meanMarginal
  rw [← he,probabilityClip_eq]
  exact ⟨(privateTypicalMixture mu xi c fixed I b).prob_nonneg _,
    (privateTypicalMixture mu xi c fixed I b).prob_le_one _⟩

structure TypicalCountParameters where
  xi : ℝ
  c : ℕ
  N : ℕ
  privateMean0 : ℝ
  privateMean1 : ℝ

namespace TypicalCountParameters

def owner0 (P : TypicalCountParameters) (M : ℕ) : ℕ :=
  min (P.N-M) (balancedOwnerQuota (P.N-M) P.privateMean0 P.privateMean1)

def owner1 (P : TypicalCountParameters) (M : ℕ) : ℕ := P.N-M-P.owner0 M

theorem owner0_le (P : TypicalCountParameters) (M : ℕ) : P.owner0 M ≤ P.N-M :=
  min_le_left _ _

theorem owner0_eq_nearest (P : TypicalCountParameters) (M : ℕ)
    (hmean : |P.privateMean1-P.privateMean0| ≤ P.N-M) :
    P.owner0 M=balancedOwnerQuota (P.N-M) P.privateMean0 P.privateMean1 := by
  have hMN : M ≤ P.N := by
    have hh := (abs_nonneg (P.privateMean1-P.privateMean0)).trans hmean
    exact_mod_cast (sub_nonneg.mp hh)
  have hmean' : |P.privateMean1-P.privateMean0| ≤ ((P.N-M : ℕ) : ℝ) := by
    simpa only [Nat.cast_sub hMN] using hmean
  exact min_eq_right
    (balancedOwnerQuota_guards (P.N-M) P.privateMean0 P.privateMean1 hmean').1

theorem owner_sum (P : TypicalCountParameters) (M : ℕ) :
    P.owner0 M+P.owner1 M=P.N-M := by
  unfold owner1
  exact Nat.add_sub_of_le (P.owner0_le M)

def mixedCount (P : TypicalCountParameters) (M : ℕ) (W bi : ℝ) : CountLaw 2 :=
  meanCountLaw P.xi P.c (P.owner0 M) (P.owner1 M)
    P.privateMean0 P.privateMean1 M W bi

end TypicalCountParameters

end FCAppendix.Affine.Tail04
