import FCAppendix.Affine.Tail04.NativePartialFiberCoordinates
import FCAppendix.Affine.Tail04.OriginalDummyCoordinate
import FCAppendix.Affine.Tail04.EqualPartialOriginalIntegral

noncomputable section
namespace FCAppendix.Affine.Tail04.NativePartialExperiment
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open NativeLocalPolicy EqualPrivateSignal EqualPrivateUpper JoinedHighPolicy
open LocalHighCommon PrivatePartialSorting AtypicalPartialNoisy SortedAllNoise
open scoped BigOperators

local instance (α : Type*) : MeasurableSpace (Finset α) := ⊤

def ownH {m : ℕ} (H0 H1 : Fin (m+1)) (side : Bool) : Fin (m+1) :=
  ⟨AllCountAtypical.ownCount H0.val H1.val side,by
    cases side
    · exact H0.isLt
    · exact H1.isLt⟩

@[simp] lemma ownH_false {m : ℕ} (H0 H1 : Fin (m+1)) : ownH H0 H1 false=H0 := rfl
@[simp] lemma ownH_true {m : ℕ} (H0 H1 : Fin (m+1)) : ownH H0 H1 true=H1 := rfl
@[simp] lemma ownH_val {m : ℕ} (H0 H1 : Fin (m+1)) (side : Bool) :
    (ownH H0 H1 side).val=AllCountAtypical.ownCount H0.val H1.val side := rfl

variable {m c : ℕ} (K : NativeLocalPolicy.Data m c) (A : ℕ) (H0 H1 : Fin (m+1))

def sampler (side : Bool) :
    (Parameters A H0.val K.E.R K.E.Rp K.E.U ×
      Row (ownH H0 H1 side).val K.E.R K.E.Rp K.E.H) →
        unitInterval → Finset (Target A (ownH H0 H1 side).val) := by
  cases side
  · exact K.zeroSampler A H0 H1
  · exact K.oneSampler A H0 H1

@[simp] lemma sampler_false : sampler K A H0 H1 false=K.zeroSampler A H0 H1 := rfl
@[simp] lemma sampler_true : sampler K A H0 H1 true=K.oneSampler A H0 H1 := rfl

lemma measurable_sampler (side : Bool) :
    Measurable (Function.uncurry (sampler K A H0 H1 side)) := by
  cases side
  · exact K.zeroSampler_measurable A H0 H1
  · exact K.oneSampler_measurable A H0 H1

def publicParameter (Q : PublicScenario.Data) (low : Bool)
    (b : Fin A → Icc (1:ℝ) K.E.U) (u : unitInterval) :
    Parameters A H0.val K.E.R K.E.Rp K.E.U :=
  JoinedPartialPublicIntegral.parameters (sortedBox b) (K.signalLaw H0)
    (NativeHighExperiment.choice K H0 H1 Q b low u)

lemma measurable_publicParameter (Q : PublicScenario.Data) (low : Bool) :
    Measurable (Function.uncurry (publicParameter K A H0 H1 Q low)) := by
  let bs : ((Fin A → Icc (1:ℝ) K.E.U)×unitInterval) → Fin A → Icc (1:ℝ) K.E.U :=
    fun z => sortedBox z.1
  have hb : Measurable bs := continuous_sortedBox.measurable.comp measurable_fst
  have hc : Measurable (fun z : (Fin A → Icc (1:ℝ) K.E.U)×unitInterval =>
      NativeHighExperiment.choice K H0 H1 Q z.1 low z.2) := by
    cases low
    · exact measurable_const
    · exact (PublicScenario.measurable_draw Q A).comp
        ((((measurable_pi_lambda _ fun j => ((measurable_pi_apply j).subtype_val.comp hb)).prodMk
          measurable_const)).prodMk measurable_snd)
  exact (hc.fst.prodMk hb).prodMk (measurable_const.prodMk hc.snd)

def inclusion (Q : PublicScenario.Data) (side low : Bool)
    (j : Fin (ownH H0 H1 side).val) (b : Fin A → Icc (1:ℝ) K.E.U)
    (row : Row (ownH H0 H1 side).val K.E.R K.E.Rp K.E.H)
    (publicSeed privateSeed : unitInterval) : ℝ :=
  if Sum.inr j∈sampler K A H0 H1 side
      (publicParameter K A H0 H1 Q low b publicSeed,row) privateSeed then 1 else 0

lemma inclusion_bounds (Q : PublicScenario.Data) (side low : Bool)
    (j : Fin (ownH H0 H1 side).val) (b : Fin A → Icc (1:ℝ) K.E.U)
    (row : Row (ownH H0 H1 side).val K.E.R K.E.Rp K.E.H) (a u : unitInterval) :
    inclusion K A H0 H1 Q side low j b row a u∈Icc (0:ℝ) 1 := by
  unfold inclusion
  split_ifs <;> norm_num

lemma measurable_inclusion (Q : PublicScenario.Data) (side low : Bool)
    (j : Fin (ownH H0 H1 side).val) :
    Measurable (fun z : (Fin A → Icc (1:ℝ) K.E.U)×
      (Row (ownH H0 H1 side).val K.E.R K.E.Rp K.E.H×(unitInterval×unitInterval)) =>
        inclusion K A H0 H1 Q side low j z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  have hp : Measurable (fun z : (Fin A → Icc (1:ℝ) K.E.U)×
      (Row (ownH H0 H1 side).val K.E.R K.E.Rp K.E.H×(unitInterval×unitInterval)) =>
      publicParameter K A H0 H1 Q low z.1 z.2.2.1) :=
    (measurable_publicParameter K A H0 H1 Q low).comp
    (measurable_fst.prodMk measurable_snd.snd.fst)
  have hs := (measurable_sampler K A H0 H1 side).comp
    ((hp.prodMk measurable_snd.fst).prodMk measurable_snd.snd.snd)
  have hmem : MeasurableSet {z : (Fin A → Icc (1:ℝ) K.E.U)×
      (Row (ownH H0 H1 side).val K.E.R K.E.Rp K.E.H×(unitInterval×unitInterval)) |
      Sum.inr j∈sampler K A H0 H1 side
        (publicParameter K A H0 H1 Q low z.1 z.2.2.1,z.2.1) z.2.2.2} := by
    exact hs (Set.to_countable {S : Finset (Target A (ownH H0 H1 side).val) |
      Sum.inr j∈S}).measurableSet
  exact Measurable.ite hmem measurable_const measurable_const

def value (Q : PublicScenario.Data) (side low : Bool)
    (j : Fin (ownH H0 H1 side).val) (v : ℝ) (price : Icc K.E.R K.E.Rp)
    (b : Fin A → Icc (1:ℝ) K.E.U)
    (row : Row (ownH H0 H1 side).val K.E.R K.E.Rp K.E.H)
    (publicSeed privateSeed : unitInterval) : ℝ :=
  (v-price)*inclusion K A H0 H1 Q side low j b row publicSeed privateSeed

lemma value_bound (Q : PublicScenario.Data) (side low : Bool)
    (j : Fin (ownH H0 H1 side).val) (v : ℝ) (price : Icc K.E.R K.E.Rp)
    (b : Fin A → Icc (1:ℝ) K.E.U)
    (row : Row (ownH H0 H1 side).val K.E.R K.E.Rp K.E.H) (a u : unitInterval) :
    |value K A H0 H1 Q side low j v price b row a u|≤|v|+K.E.Rp := by
  have hi := inclusion_bounds K A H0 H1 Q side low j b row a u
  have hp : 0≤(price:ℝ) := (K.E.d_nonneg.trans K.E.d_lt_R.le).trans price.2.1
  rw [value,abs_mul,abs_of_nonneg hi.1]
  calc
    _≤|v-price| := mul_le_of_le_one_right (abs_nonneg _) hi.2
    _≤|v|+|((price:ℝ))| := abs_sub _ _
    _≤|v|+K.E.Rp := by rw [abs_of_nonneg hp];linarith [price.2.2]

section Noise
variable {Up eps : ℝ} (heps : 0≤ eps) (hRp : K.E.Rp=Up*(1+eps))

def noisyPrice (b : Icc K.E.R Up) (z : unitInterval) : Icc K.E.R K.E.Rp :=
  hRp.symm ▸ (⟨Hybrid.activeNoisyRealBid eps b z,
    Hybrid.activeNoisyRealBid_mem (K.E.d_nonneg.trans_lt K.E.d_lt_R) heps b z⟩ :
      Icc K.E.R (Up*(1+eps)))

lemma measurable_noisyPrice (b : Icc K.E.R Up) : Measurable (noisyPrice K heps hRp b) := by
  rcases K with ⟨E,ξ,w,π,hξ,hξ1,hw,hπ,hrare,hdup,rows,hupper,choose,hchoose⟩
  rcases E with ⟨d,R,Rp,U,H,hd,hdR,hRRp,hRp1,hU,hUH⟩
  change Rp=Up*(1+eps) at hRp
  cases hRp
  exact ((continuous_const.mul (continuous_const.add (continuous_const.mul continuous_subtype_val))).subtype_mk _).measurable

def noisyValue (Q : PublicScenario.Data) (side low : Bool)
    (j : Fin (ownH H0 H1 side).val) (v : ℝ) (price : Icc K.E.R Up)
    (b : Fin A → Icc (1:ℝ) K.E.U)
    (row : Row (ownH H0 H1 side).val K.E.R K.E.Rp K.E.H)
    (z publicSeed privateSeed : unitInterval) : ℝ :=
  value K A H0 H1 Q side low j v (noisyPrice K heps hRp price z) b
    (Function.update row j (Sum.inr (noisyPrice K heps hRp price z))) publicSeed privateSeed

lemma measurable_noisyValue (Q : PublicScenario.Data) (side low : Bool)
    (j : Fin (ownH H0 H1 side).val) (v : ℝ) (price : Icc K.E.R Up) :
    Measurable (fun x : (Fin A → Icc (1:ℝ) K.E.U)×
      (Row (ownH H0 H1 side).val K.E.R K.E.Rp K.E.H×
        (unitInterval×(unitInterval×unitInterval))) =>
      noisyValue K A H0 H1 heps hRp Q side low j v price x.1 x.2.1
        x.2.2.1 x.2.2.2.1 x.2.2.2.2) := by
  have hp : Measurable (fun x : (Fin A → Icc (1:ℝ) K.E.U)×
      (Row (ownH H0 H1 side).val K.E.R K.E.Rp K.E.H×
        (unitInterval×(unitInterval×unitInterval))) =>
      noisyPrice K heps hRp price x.2.2.1) :=
    (measurable_noisyPrice K heps hRp price).comp measurable_snd.snd.fst
  have hr : Measurable (fun x : (Fin A → Icc (1:ℝ) K.E.U)×
      (Row (ownH H0 H1 side).val K.E.R K.E.Rp K.E.H×
        (unitInterval×(unitInterval×unitInterval))) =>
      Function.update x.2.1 j (Sum.inr (noisyPrice K heps hRp price x.2.2.1))) := by
    apply measurable_pi_lambda
    intro k
    by_cases hk : k=j
    · subst k
      simpa only [Function.update_self,Function.comp_apply] using! measurable_inr.comp hp
    · simpa only [Function.update_of_ne hk,Function.comp_apply] using!
        (measurable_pi_apply k).comp measurable_snd.fst
  have hi := (measurable_inclusion K A H0 H1 Q side low j).comp
    (measurable_fst.prodMk (hr.prodMk measurable_snd.snd.snd))
  have hv := ((measurable_const (a:=v)).sub hp.subtype_val).mul hi
  exact hv

lemma noisyValue_bound (Q : PublicScenario.Data) (side low : Bool)
    (j : Fin (ownH H0 H1 side).val) (v : ℝ) (price : Icc K.E.R Up)
    (b : Fin A → Icc (1:ℝ) K.E.U)
    (row : Row (ownH H0 H1 side).val K.E.R K.E.Rp K.E.H) (z a u : unitInterval) :
    |noisyValue K A H0 H1 heps hRp Q side low j v price b row z a u|≤|v|+K.E.Rp :=
  value_bound K A H0 H1 Q side low j v _ b _ a u

end Noise

theorem integral_swap_bounded {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : X×Y→ℝ) (hf : Measurable f) (C : ℝ) (hC : ∀ z,‖f z‖≤ C) :
    (∫ x,∫ y,f (x,y) ∂ν ∂μ)=∫ y,∫ x,f (x,y) ∂μ ∂ν :=
  integral_integral_swap (Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC))

lemma update_cast_cons {X : Type*} {h k : ℕ} (he : h=k+1)
    (x d : X) (row : Fin k → X) :
    Function.update ((Fin.cons d row) ∘ Fin.cast he) (Fin.cast he.symm 0) x=
      (Fin.cons x row) ∘ Fin.cast he := by
  cases he
  funext j
  refine Fin.cases ?_ (fun q => ?_) j
  · simp
  · simp

lemma integral_update_cast {X : Type*} [MeasurableSpace X] {h k : ℕ}
    (he : h=k+1) (ρ : Measure X) [IsProbabilityMeasure ρ]
    (x : X) (f : (Fin h→ X)→ℝ) (hf : Measurable f) (C : ℝ) (hC : ∀ row,‖f row‖≤ C) :
    (∫ row,f (Function.update row (Fin.cast he.symm 0) x)
      ∂Measure.pi (fun _ : Fin h => ρ))=
      ∫ row,f ((Fin.cons x row) ∘ Fin.cast he) ∂Measure.pi (fun _ : Fin k => ρ) := by
  cases he
  exact OriginalDummyCoordinate.integral_update_zero ρ x f hf C hC

lemma measurable_option_default : Measurable (fun x : Option unitInterval×unitInterval => x.1.getD x.2) := by
  have hi : Measurable (fun o : Option unitInterval => o.isSome) := by
    intro S hS
    change MeasurableSet ((fun _ : unitInterval => true) ⁻¹' S)
    exact measurable_const hS
  have hg : Measurable (fun o : Option unitInterval => o.getD 0) := by
    intro S hS
    change MeasurableSet S
    exact hS
  have he : (fun x : Option unitInterval×unitInterval => x.1.getD x.2)=
      fun x => if x.1.isSome then x.1.getD 0 else x.2 := by
    funext x
    rcases x with ⟨o,u⟩
    cases o <;> rfl
  rw [he]
  exact Measurable.ite (measurableSet_eq_fun (hi.comp measurable_fst) measurable_const)
    (hg.comp measurable_fst) measurable_snd

end FCAppendix.Affine.Tail04.NativePartialExperiment
