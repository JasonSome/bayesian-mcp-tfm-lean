import FCAppendix.Affine.Uniform06.SamplingCoefficientBounds
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Logic.Equiv.Fintype
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
namespace FCAppendix.Affine.Uniform06.FiniteMarkedExchangeability

open MeasureTheory Set
open scoped BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in

theorem integral_permute_iid (μ : Measure Ω) [SigmaFinite μ]
    (π : Equiv.Perm ι) (F : (ι → Ω) → ℝ) :
    (∫ ω,F (fun j => ω (π j)) ∂Measure.pi (fun _ : ι => μ))=
      ∫ ω,F ω ∂Measure.pi (fun _ : ι => μ) := by
  have hh := (measurePreserving_piCongrLeft (fun _ : ι => μ) π.symm).integral_comp' F
  convert! hh using 1
  congr 1
  funext ω
  congr 1
  funext j
  simp only [MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply,
    eq_rec_constant,Equiv.symm_symm]

omit [DecidableEq ι] in

theorem integral_selected_tuple_eq (μ : Measure Ω) [SigmaFinite μ]
    {k : ℕ} (f g : Fin k ↪ ι)
    (F : (ι → Ω) → (Fin k → Ω) → ℝ)
    (hsym : ∀ (π : Equiv.Perm ι) ω marks,F (fun j => ω (π j)) marks=F ω marks) :
    (∫ ω,F ω (fun j => ω (f j)) ∂Measure.pi (fun _ : ι => μ))=
      ∫ ω,F ω (fun j => ω (g j)) ∂Measure.pi (fun _ : ι => μ) := by
  obtain ⟨π,hπ⟩ := Equiv.Perm.exists_extending_pair f g f.injective g.injective
  have hh := integral_permute_iid μ π (fun ω => F ω (fun j => ω (f j)))
  rw [← hh]
  apply integral_congr_ae
  exact ae_of_all _ fun ω => by
    dsimp only
    rw [hsym]
    congr 1
    funext j
    rw [hπ j]

omit [DecidableEq ι] in

theorem integral_distinct_sum (μ : Measure Ω) [SigmaFinite μ]
    {k : ℕ} (f0 : Fin k ↪ ι)
    (F : (ι → Ω) → (Fin k → Ω) → ℝ)
    (hsym : ∀ (π : Equiv.Perm ι) ω marks,F (fun j => ω (π j)) marks=F ω marks)
    (hI : ∀ f : Fin k ↪ ι,Integrable (fun ω => F ω (fun j => ω (f j)))
      (Measure.pi (fun _ : ι => μ))) :
    (∫ ω,∑ f : Fin k ↪ ι,F ω (fun j => ω (f j)) ∂Measure.pi (fun _ : ι => μ))=
      ((Fintype.card ι).descFactorial k:ℝ)*
        ∫ ω,F ω (fun j => ω (f0 j)) ∂Measure.pi (fun _ : ι => μ) := by
  classical
  rw [integral_finsetSum Finset.univ (fun f _ => hI f)]
  simp_rw [integral_selected_tuple_eq μ _ f0 F hsym]
  simp [Fintype.card_embedding_eq]

theorem measurePreserving_append (μ : Measure Ω) [SigmaFinite μ] (k N : ℕ) :
    MeasurePreserving (fun p : (Fin k → Ω) × (Fin N → Ω) => Fin.append p.1 p.2)
      ((Measure.pi (fun _ : Fin k => μ)).prod (Measure.pi (fun _ : Fin N => μ)))
      (Measure.pi (fun _ : Fin (k+N) => μ)) := by
  have hs := measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin k ⊕ Fin N => μ)
  have hr := measurePreserving_piCongrLeft (fun _ : Fin (k+N) => μ) finSumFinEquiv
  convert! hr.comp hs using 1
  funext p j
  refine Fin.addCases ?_ ?_ j <;> intro q <;>
    simp [MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply,
      MeasurableEquiv.sumPiEquivProdPi,Fin.append]

private theorem measurableEmbedding_append (k N : ℕ) :
    MeasurableEmbedding (fun p : (Fin k → Ω) × (Fin N → Ω) => Fin.append p.1 p.2) := by
  let e := (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin k ⊕ Fin N => Ω)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (k+N) => Ω) finSumFinEquiv)
  convert! e.measurableEmbedding using 1
  funext p j
  refine Fin.addCases ?_ ?_ j <;> intro q <;>
    simp [e,MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply,
      MeasurableEquiv.sumPiEquivProdPi,Fin.append]

def sumX (X : Ω → ℝ) {N : ℕ} (ω : Fin N → Ω) : ℝ := ∑ j,X (ω j)
def sumY (Y : Ω → ℤ) {N : ℕ} (ω : Fin N → Ω) : ℤ := ∑ j,Y (ω j)

def laplace (X : Ω → ℝ) (Y : Ω → ℤ) (cap θ : ℝ) (y : ℤ) (r : ℕ)
    {N : ℕ} (ω : Fin N → Ω) : ℝ :=
  if sumY Y ω=y ∧ 0 < cap-sumX X ω then
    Real.exp (-θ*(cap-sumX X ω))*(cap-sumX X ω)^r else 0

def markedFunctional (X h w : Ω → ℝ) (Y : Ω → ℤ)
    (cap θ : ℝ) (y : ℤ) (r : ℕ) {N k : ℕ}
    (ω : Fin N → Ω) (marks : Fin k → Ω) : ℝ :=
  (∏ j,w (marks j))*
    if sumY Y ω=y ∧ 0 < cap-sumX X ω-sumX h marks then
      Real.exp (-θ*(cap-sumX X ω))*(cap-sumX X ω-sumX h marks)^r else 0

omit [MeasurableSpace Ω] in
theorem markedFunctional_symmetric (X h w : Ω → ℝ) (Y : Ω → ℤ)
    (cap θ : ℝ) (y : ℤ) (r : ℕ) {N k : ℕ}
    (π : Equiv.Perm (Fin N)) (ω : Fin N → Ω) (marks : Fin k → Ω) :
    markedFunctional X h w Y cap θ y r (fun j => ω (π j)) marks=
      markedFunctional X h w Y cap θ y r ω marks := by
  have hx := π.sum_comp Finset.univ (fun j => X (ω j)) (by simp)
  have hy := π.sum_comp Finset.univ (fun j => Y (ω j)) (by simp)
  simp only [markedFunctional,sumX,sumY,hx,hy]

omit [MeasurableSpace Ω] in

theorem selected_factorization (X h w : Ω → ℝ) (Y : Ω → ℤ)
    (hsupport : ∀ x,w x ≠ 0 → X x+h x=1/2 ∧ Y x=0)
    (cap θ : ℝ) (y : ℤ) (r : ℕ) {k N : ℕ}
    (marks : Fin k → Ω) (ω : Fin N → Ω) :
    markedFunctional X h w Y cap θ y r (Fin.append marks ω) marks=
      (∏ j,w (marks j)*Real.exp (-θ*h (marks j)))*
        laplace X Y (cap-(k:ℝ)/2) θ y r ω := by
  classical
  by_cases hz : ∃ j,w (marks j)=0
  · obtain ⟨j,hj⟩ := hz
    have hw0 : (∏ q,w (marks q))=0 := Finset.prod_eq_zero (Finset.mem_univ j) hj
    have he0 : (∏ q,w (marks q)*Real.exp (-θ*h (marks q)))=0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hj,zero_mul])
    simp only [neg_mul] at he0
    simp [markedFunctional,hw0,he0]
  have hall (j : Fin k) := hsupport (marks j) (fun hj => hz ⟨j,hj⟩)
  have hx : sumX X marks+sumX h marks=(k:ℝ)/2 := by
    rw [sumX,sumX,← Finset.sum_add_distrib]
    simp_rw [(hall _).1]
    simp [div_eq_mul_inv]
  have hy : sumY Y marks=0 := by
    exact Finset.sum_eq_zero (fun j _ => (hall j).2)
  have hxa : sumX X (Fin.append marks ω)=sumX X marks+sumX X ω := by
    unfold sumX
    rw [Fin.sum_univ_add]
    simp
  have hya : sumY Y (Fin.append marks ω)=sumY Y ω := by
    unfold sumY at *
    rw [Fin.sum_univ_add]
    simp [hy]
  have hd : cap-(sumX X marks+sumX X ω)-sumX h marks=
      cap-(k:ℝ)/2-sumX X ω := by linarith
  have hexp : (∏ j,w (marks j)*Real.exp (-θ*h (marks j)))=
      (∏ j,w (marks j))*Real.exp (-θ*sumX h marks) := by
    rw [Finset.prod_mul_distrib,← Real.exp_sum]
    congr 2
    rw [sumX,Finset.mul_sum]
  rw [markedFunctional,hxa,hya,hd,hexp,laplace]
  split_ifs with hc
  · have he : Real.exp (-θ*(cap-(sumX X marks+sumX X ω)))=
        Real.exp (-θ*sumX h marks)*Real.exp (-θ*(cap-(k:ℝ)/2-sumX X ω)) := by
      rw [← Real.exp_add]
      congr 1
      nlinarith [congrArg (fun q : ℝ => θ*q) hx]
    rw [he]
    ring
  · simp

theorem integral_selected_prefix_factorization (μ : Measure Ω) [SigmaFinite μ]
    (X h w : Ω → ℝ) (Y : Ω → ℤ)
    (hsupport : ∀ x,w x ≠ 0 → X x+h x=1/2 ∧ Y x=0)
    (cap θ : ℝ) (y : ℤ) (r k N : ℕ) :
    (∫ row : Fin (k+N) → Ω,markedFunctional X h w Y cap θ y r row
      (fun j : Fin k => row (Fin.castAdd N j)) ∂Measure.pi (fun _ : Fin (k+N) => μ))=
      (∫ x,w x*Real.exp (-θ*h x) ∂μ)^k*
        ∫ row : Fin N → Ω,laplace X Y (cap-(k:ℝ)/2) θ y r row
          ∂Measure.pi (fun _ : Fin N => μ) := by
  have hp := (measurePreserving_append μ k N).integral_comp
    (measurableEmbedding_append k N)
    (fun row : Fin (k+N) → Ω => markedFunctional X h w Y cap θ y r row
      (fun j : Fin k => row (Fin.castAdd N j)))
  rw [← hp]
  have he : (fun p : (Fin k → Ω) × (Fin N → Ω) =>
      markedFunctional X h w Y cap θ y r (Fin.append p.1 p.2)
        (fun j => Fin.append p.1 p.2 (Fin.castAdd N j)))=
      fun p => (∏ j,w (p.1 j)*Real.exp (-θ*h (p.1 j)))*
        laplace X Y (cap-(k:ℝ)/2) θ y r p.2 := by
    funext p
    simp only [Fin.append_left]
    exact selected_factorization X h w Y hsupport cap θ y r p.1 p.2
  rw [he,integral_prod_mul
    (fun marks : Fin k → Ω => ∏ j,w (marks j)*Real.exp (-θ*h (marks j)))
    (fun row : Fin N → Ω => laplace X Y (cap-(k:ℝ)/2) θ y r row)]
  rw [integral_fintype_prod_eq_pow (ι := Fin k) (fun x => w x*Real.exp (-θ*h x))]
  simp only [Fintype.card_fin]

theorem literal_distinct_laplace_identity (μ : Measure Ω) [SigmaFinite μ]
    (X h w : Ω → ℝ) (Y : Ω → ℤ)
    (hsupport : ∀ x,w x ≠ 0 → X x+h x=1/2 ∧ Y x=0)
    (cap θ : ℝ) (y : ℤ) (r k N : ℕ)
    (hI : ∀ f : Fin k ↪ Fin (k+N),Integrable
      (fun ω => markedFunctional X h w Y cap θ y r ω (fun j => ω (f j)))
        (Measure.pi (fun _ : Fin (k+N) => μ))) :
    (∫ ω : Fin (k+N) → Ω,∑ f : Fin k ↪ Fin (k+N),
      markedFunctional X h w Y cap θ y r ω (fun j => ω (f j))
        ∂Measure.pi (fun _ : Fin (k+N) => μ))=
      ((k+N).descFactorial k:ℝ)*(∫ x,w x*Real.exp (-θ*h x) ∂μ)^k*
        ∫ row : Fin N → Ω,laplace X Y (cap-(k:ℝ)/2) θ y r row
          ∂Measure.pi (fun _ : Fin N => μ) := by
  let f0 : Fin k ↪ Fin (k+N) := Fin.castAddEmb N
  rw [integral_distinct_sum μ f0 (markedFunctional X h w Y cap θ y r)
    (markedFunctional_symmetric X h w Y cap θ y r) hI]
  simp only [Fintype.card_fin]
  change ((k+N).descFactorial k:ℝ)*(∫ row : Fin (k+N) → Ω,
    markedFunctional X h w Y cap θ y r row (fun j => row (Fin.castAdd N j))
      ∂Measure.pi (fun _ : Fin (k+N) => μ))=_
  rw [integral_selected_prefix_factorization μ X h w Y hsupport cap θ y r k N]
  ring

end FCAppendix.Affine.Uniform06.FiniteMarkedExchangeability
