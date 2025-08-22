import Mathlib

variable {ι κ μ K : Type*} [Field K]

noncomputable def jacobian (p : ι → MvPolynomial κ K) : Matrix ι κ (MvPolynomial κ K) :=
  fun i j => (p i).pderiv j

noncomputable def comp (p : ι → MvPolynomial κ K) (q : κ → MvPolynomial μ K) :
    ι → MvPolynomial μ K :=
  fun i => (p i).bind₁ q

def eval (p : ι → MvPolynomial κ K) : (κ → K) → (ι → K) :=
  fun x i => (p i).eval x

@[simp]
lemma eval_comp (p : ι → MvPolynomial κ K) (q : κ → MvPolynomial μ K) : eval (comp p q) = eval p ∘ eval q := by
  ext x i
  simp [eval, comp]
  delta eval
  rw [MvPolynomial.eval, MvPolynomial.eval₂Hom_bind₁]
  simp

lemma MvPolynomial.pderiv_bind₁ {σ : Type*} [Fintype σ]
    (p : MvPolynomial σ K) (q : σ → MvPolynomial ι K) (i : ι) :
    (p.bind₁ q).pderiv i = ∑ j : σ, ((p.pderiv j).bind₁ q) * (q j).pderiv i  := by
  induction p using MvPolynomial.induction_on with
  | C => simp
  | add f g ihf ihg =>
    rw [map_add, map_add, ihf, ihg]
    simp [add_mul, Finset.sum_add_distrib]
  | mul_X f j ih =>
    rw [map_mul, bind₁_X_right, pderiv_mul, ih]
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, bind₁_X_right, add_mul]
    rw [Finset.sum_add_distrib, eq_comm, Finset.sum_eq_single j]
    · simp only [pderiv_X_self, map_one, mul_comm, one_mul, mul_left_comm, add_comm, Finset.mul_sum]
    · intro k hk hkj
      rw [pderiv_X_of_ne hkj.symm]
      simp
    · simp

lemma jacobian_comp [Fintype ι] [Fintype κ] [Fintype μ] (p : ι → MvPolynomial κ K) (q : κ → MvPolynomial μ K) (x : μ → K) :
    (jacobian (comp p q)).map (MvPolynomial.eval x) =
      (jacobian p).map (MvPolynomial.eval (fun i => (q i).eval x)) * (jacobian q).map (MvPolynomial.eval x) := by
  apply Matrix.ext
  intro i j
  delta jacobian comp
  simp [Matrix.mul_apply, MvPolynomial.pderiv_bind₁]
  refine Finset.sum_congr rfl ?_
  intro k _
  simp
  rw [MvPolynomial.eval, MvPolynomial.eval₂Hom_bind₁]
  simp

lemma jacobian_add (p q : ι → MvPolynomial κ K) :
    jacobian (p + q) = jacobian p + jacobian q := by
  ext1 i j
  simp [jacobian]
