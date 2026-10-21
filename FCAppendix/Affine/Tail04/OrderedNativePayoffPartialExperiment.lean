import FCAppendix.Affine.Tail04.NativePartialC1Integral
import FCAppendix.Affine.Tail04.OrderedNativePayoffBindings

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedNativePayoffPartialExperiment
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open NativeLocalPolicy EqualPrivateSignal EqualPrivateUpper JoinedHighPolicy
open NativePartialExperiment NativePartialProductReduction

variable {m c : ℕ} (K : NativeLocalPolicy.Data m c) (A : ℕ)
  (own other : Fin (m+1)) (physical : Fin 2) (Q : PublicScenario.Data)

def inclusion (low : Bool) (j : Fin own.val)
    (b : Fin A → Icc (1:ℝ) K.E.U)
    (row : Row own.val K.E.R K.E.Rp K.E.H) (publicSeed privateSeed : unitInterval) : ℝ :=
  if OrderedHigherRoles.first physical own.val other.val then
    NativePartialExperiment.inclusion K A own other Q false low j b row publicSeed privateSeed
  else NativePartialExperiment.inclusion K A other own Q true low j b row publicSeed privateSeed

lemma measurable_inclusion (low : Bool) (j : Fin own.val) :
    Measurable (fun x : (Fin A → Icc (1:ℝ) K.E.U)×
      (Row own.val K.E.R K.E.Rp K.E.H×(unitInterval×unitInterval)) =>
        inclusion K A own other physical Q low j x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  unfold inclusion
  split
  · exact NativePartialExperiment.measurable_inclusion K A own other Q false low j
  · exact NativePartialExperiment.measurable_inclusion K A other own Q true low j

lemma inclusion_bounds (low : Bool) (j : Fin own.val)
    (b : Fin A → Icc (1:ℝ) K.E.U)
    (row : Row own.val K.E.R K.E.Rp K.E.H) (a u : unitInterval) :
    inclusion K A own other physical Q low j b row a u∈Icc (0:ℝ) 1 := by
  unfold inclusion
  split
  · exact NativePartialExperiment.inclusion_bounds K A own other Q false low j b row a u
  · exact NativePartialExperiment.inclusion_bounds K A other own Q true low j b row a u

def value (low : Bool) (j : Fin own.val) (v : ℝ) (price : Icc K.E.R K.E.Rp)
    (b : Fin A → Icc (1:ℝ) K.E.U)
    (row : Row own.val K.E.R K.E.Rp K.E.H) (a u : unitInterval) : ℝ :=
  (v-price)*inclusion K A own other physical Q low j b row a u

lemma measurable_value (low : Bool) (j : Fin own.val) (v : ℝ) :
    Measurable (fun x : Icc K.E.R K.E.Rp×((Fin A→Icc (1:ℝ) K.E.U)×
      (Row own.val K.E.R K.E.Rp K.E.H×(unitInterval×unitInterval)))=>
      value K A own other physical Q low j v x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) :=
  (measurable_const.sub measurable_fst.subtype_val).mul
    ((measurable_inclusion K A own other physical Q low j).comp measurable_snd)

lemma value_first (h : OrderedHigherRoles.first physical own.val other.val)
    (low : Bool) (j : Fin own.val) (v : ℝ) (price : Icc K.E.R K.E.Rp)
    (b : Fin A → Icc (1:ℝ) K.E.U)
    (row : Row own.val K.E.R K.E.Rp K.E.H) (a u : unitInterval) :
    value K A own other physical Q low j v price b row a u=
      NativePartialExperiment.value K A own other Q false low j v price b row a u := by
  simp only [value,inclusion,if_pos h,NativePartialExperiment.value]

lemma value_second (h : ¬OrderedHigherRoles.first physical own.val other.val)
    (low : Bool) (j : Fin own.val) (v : ℝ) (price : Icc K.E.R K.E.Rp)
    (b : Fin A → Icc (1:ℝ) K.E.U)
    (row : Row own.val K.E.R K.E.Rp K.E.H) (a u : unitInterval) :
    value K A own other physical Q low j v price b row a u=
      NativePartialExperiment.value K A other own Q true low j v price b row a u := by
  simp only [value,inclusion,if_neg h,NativePartialExperiment.value]

lemma value_bound (low : Bool) (j : Fin own.val) (v : ℝ) (price : Icc K.E.R K.E.Rp)
    (b : Fin A → Icc (1:ℝ) K.E.U)
    (row : Row own.val K.E.R K.E.Rp K.E.H) (a u : unitInterval) :
    |value K A own other physical Q low j v price b row a u|≤|v|+K.E.Rp := by
  by_cases h : OrderedHigherRoles.first physical own.val other.val
  · rw [value_first K A own other physical Q h]
    exact NativePartialExperiment.value_bound K A own other Q false low j v price b row a u
  · rw [value_second K A own other physical Q h]
    exact NativePartialExperiment.value_bound K A other own Q true low j v price b row a u

section Noise
variable {Up eps : ℝ} (heps : 0≤eps) (hRp : K.E.Rp=Up*(1+eps))

def noisyValue (low : Bool) (j : Fin own.val) (v : ℝ) (price : Icc K.E.R Up)
    (b : Fin A → Icc (1:ℝ) K.E.U)
    (row : Row own.val K.E.R K.E.Rp K.E.H) (z a u : unitInterval) : ℝ :=
  value K A own other physical Q low j v (noisyPrice K heps hRp price z) b
    (Function.update row j (Sum.inr (noisyPrice K heps hRp price z))) a u

lemma measurable_noisyValue (low : Bool) (j : Fin own.val) (v : ℝ) (price : Icc K.E.R Up) :
    Measurable (fun x : (Fin A → Icc (1:ℝ) K.E.U)×
      (Row own.val K.E.R K.E.Rp K.E.H×(unitInterval×(unitInterval×unitInterval))) =>
        noisyValue K A own other physical Q heps hRp low j v price
          x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) := by
  by_cases h : OrderedHigherRoles.first physical own.val other.val
  · simpa only [noisyValue,value_first K A own other physical Q h,
      NativePartialExperiment.noisyValue] using!
        NativePartialExperiment.measurable_noisyValue K A own other heps hRp Q false low j v price
  · simpa only [noisyValue,value_second K A own other physical Q h,
      NativePartialExperiment.noisyValue] using!
        NativePartialExperiment.measurable_noisyValue K A other own heps hRp Q true low j v price

lemma noisyValue_bound (low : Bool) (j : Fin own.val) (v : ℝ) (price : Icc K.E.R Up)
    (b : Fin A → Icc (1:ℝ) K.E.U)
    (row : Row own.val K.E.R K.E.Rp K.E.H) (z a u : unitInterval) :
    |noisyValue K A own other physical Q heps hRp low j v price b row z a u|≤|v|+K.E.Rp :=
  value_bound K A own other physical Q low j v _ b _ a u

end Noise

end FCAppendix.Affine.Tail04.OrderedNativePayoffPartialExperiment
