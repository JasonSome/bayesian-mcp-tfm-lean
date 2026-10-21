import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.Composition.Lemmas

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryCommonCarrier

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

abbrev History (n : ℕ) := (j : Finset.Iic n) → ℝ
abbrev Space := ℝ × (ℕ → ℝ)

def origin (n : ℕ) (h : History n) : ℝ := h ⟨0,by simp⟩
def initial (v : ℝ) : History 0 := fun _ => v

theorem measurable_origin (n : ℕ) : Measurable (origin n) :=
  measurable_pi_apply _

theorem measurable_initial : Measurable initial :=
  measurable_pi_lambda _ fun _ => measurable_id

variable (κ : ℕ → Kernel ℝ ℝ) [∀ n, IsMarkovKernel (κ n)]

def step (n : ℕ) : Kernel (History n) ℝ :=
  (κ n).comap (origin n) (measurable_origin n)

instance step_markov (n : ℕ) : IsMarkovKernel (step κ n) :=
  inferInstanceAs (IsMarkovKernel ((κ n).comap (origin n) (measurable_origin n)))

def trajectory : Kernel ℝ (ℕ → ℝ) :=
  (Kernel.traj (X := fun _ : ℕ => ℝ) (step κ) 0).comap initial measurable_initial

instance trajectory_markov : IsMarkovKernel (trajectory κ) :=
  inferInstanceAs (IsMarkovKernel
    ((Kernel.traj (X := fun _ : ℕ => ℝ) (step κ) 0).comap initial measurable_initial))

theorem partial_origin (v : ℝ) (n : ℕ) :
    ∀ᵐ h ∂(Kernel.partialTraj (X := fun _ : ℕ => ℝ) (step κ) 0 n) (initial v),origin n h=v := by
  have hproj := Kernel.partialTraj_map_frestrictLe₂_apply
    (X := fun _ : ℕ => ℝ) (κ := step κ) (initial v) (Nat.zero_le n)
  have hmap := congrArg (fun ν : Measure (History 0) => ν.map (origin 0)) hproj
  rw [Measure.map_map (measurable_origin 0)
    (measurable_pi_lambda _ fun j => measurable_pi_apply _)] at hmap
  have hcomp : origin 0 ∘ Preorder.frestrictLe₂ (π := fun _ : ℕ=>ℝ) (Nat.zero_le n)=origin n := by
    funext h
    rfl
  rw [hcomp,Kernel.partialTraj_self] at hmap
  have hdir : (((Kernel.id : Kernel (History 0) (History 0)) (initial v)).map
      (origin 0))=Measure.dirac v := by
    simp [Kernel.id_apply,origin,initial]
  rw [hdir] at hmap
  have hh : ∀ᵐ z ∂Measure.dirac v,z=v := by simp
  rw [← hmap] at hh
  exact ae_of_ae_map (measurable_origin n).aemeasurable hh

theorem trajectory_coordinate (v : ℝ) (n : ℕ) :
    ((trajectory κ) v).map (fun ω => ω (n+1))=κ n v := by
  change ((Kernel.traj (X := fun _ : ℕ => ℝ) (step κ) 0) (initial v)).map
    (fun ω => ω (n+1))=κ n v
  have hp := Kernel.partialTraj_compProd_eq_map_traj
    (X := fun _ : ℕ => ℝ) (κ := step κ) (x₀ := initial v) (Nat.zero_le n)
  have hpair : Measurable (fun ω : ℕ → ℝ =>
      (Preorder.frestrictLe n ω,ω (n+1))) :=
    (measurable_pi_lambda _ fun j => measurable_pi_apply j.val).prodMk (measurable_pi_apply _)
  ext A hA
  calc
    (((Kernel.traj (X := fun _ : ℕ => ℝ) (step κ) 0) (initial v)).map (fun ω => ω (n+1))) A
        = (((Kernel.partialTraj (X := fun _ : ℕ => ℝ) (step κ) 0 n) (initial v)).compProd (step κ n))
            (univ ×ˢ A) := by
          rw [hp,Measure.map_apply (measurable_pi_apply (n+1)) hA,
            Measure.map_apply hpair (MeasurableSet.univ.prod hA)]
          congr 1
          ext ω
          simp
    _ = ∫⁻ h,κ n (origin n h) A ∂(Kernel.partialTraj (X := fun _ : ℕ => ℝ) (step κ) 0 n) (initial v) := by
          rw [Measure.compProd_apply_prod MeasurableSet.univ hA,setLIntegral_univ]
          rfl
    _ = ∫⁻ _h,κ n v A ∂(Kernel.partialTraj (X := fun _ : ℕ => ℝ) (step κ) 0 n) (initial v) :=
          lintegral_congr_ae ((partial_origin κ v n).mono fun h hh => by
            change κ n (origin n h) A=κ n v A
            rw [hh])
    _ = κ n v A := by simp

theorem trajectory_map (n : ℕ) :
    (trajectory κ).map (fun ω => ω (n+1))=κ n := by
  ext v A hA
  rw [Kernel.map_apply _ (measurable_pi_apply _)]
  exact congrArg (fun ν : Measure ℝ => ν A) (trajectory_coordinate κ v n)

def law (F : Measure ℝ) : Measure Space := F.compProd (trajectory κ)

instance law_probability (F : Measure ℝ) [IsProbabilityMeasure F] :
    IsProbabilityMeasure (law κ F) := by unfold law; infer_instance

theorem law_value (F : Measure ℝ) [IsProbabilityMeasure F] :
    (law κ F).map Prod.fst=F := by
  change (F.compProd (trajectory κ)).fst=F
  exact Measure.fst_compProd F (trajectory κ)

theorem law_pair (F : Measure ℝ) [IsProbabilityMeasure F] (n : ℕ) :
    (law κ F).map (fun ω : Space => (ω.1,ω.2 (n+1)))=F.compProd (κ n) := by
  change (F.compProd (trajectory κ)).map
    (Prod.map id (fun ω : ℕ → ℝ => ω (n+1)))=F.compProd (κ n)
  rw [← Measure.compProd_map (measurable_pi_apply _),trajectory_map κ n]

def commonLaw (G : ℕ → ProbabilityMeasure (ℝ × ℝ)) (F : Measure ℝ) : Measure Space :=
  law (fun n => (G n:Measure (ℝ × ℝ)).condKernel) F

instance commonLaw_probability (G : ℕ → ProbabilityMeasure (ℝ × ℝ))
    (F : Measure ℝ) [IsProbabilityMeasure F] : IsProbabilityMeasure (commonLaw G F) := by
  unfold commonLaw
  infer_instance

theorem commonLaw_pair (G : ℕ → ProbabilityMeasure (ℝ × ℝ))
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF : ∀ n,(G n:Measure (ℝ × ℝ)).map Prod.fst=F) (n : ℕ) :
    (commonLaw G F).map (fun ω : Space => (ω.1,ω.2 (n+1)))=(G n:Measure (ℝ × ℝ)) := by
  rw [commonLaw,law_pair]
  have hf : (G n:Measure (ℝ × ℝ)).fst=F := hF n
  rw [← hf]
  exact (G n:Measure (ℝ × ℝ)).disintegrate _

theorem commonLaw_value (G : ℕ → ProbabilityMeasure (ℝ × ℝ))
    (F : Measure ℝ) [IsProbabilityMeasure F] :
    (commonLaw G F).map Prod.fst=F := law_value _ F

end FCAppendix.Affine.Uniform06.EntryCommonCarrier
