/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Pauli matrices

This file defines the three Pauli matrices as a family `Matrix.pauli : Fin 3 → Matrix (Fin 2)
(Fin 2) ℂ` and proves their basic algebraic properties: they are Hermitian, traceless,
involutive, of determinant `-1`, they are trace-orthogonal, and their commutators and
anticommutators close on the family.

## Main definitions

  * `Matrix.pauli`: the three Pauli matrices `σ₁`, `σ₂`, `σ₃`, indexed by `Fin 3`.
  * `Matrix.pauliSum`: the four-element family `σ^μ = (1, σ₁, σ₂, σ₃)` indexed by `Fin 1 ⊕ Fin 3`,
    used in physics as the components of a spacetime four-vector.
  * `Matrix.pauliVector`: the matrix `v · σ = ∑ i, v i • σᵢ` associated with a vector `v`.

## Main statements

  * `Matrix.isHermitian_pauli`: each `σᵃ` is Hermitian.
  * `Matrix.trace_pauli`: each `σᵃ` is traceless.
  * `Matrix.pauli_mul_self`: `σᵃ * σᵃ = 1`.
  * `Matrix.det_pauli`: `det σᵃ = -1`.
  * `Matrix.trace_pauli_mul_pauli`: the trace-orthogonality relation `Tr (σᵃ σᵇ) = 2 δᵃᵇ`.
  * `Matrix.pauli_mul_add_mul_pauli`: the anticommutation relation `{σᵃ, σᵇ} = 2 δᵃᵇ • 1`.
  * `Matrix.pauliVector_commutator`: the commutation relation in index-free form,
    `⁅v · σ, w · σ⁆ = 2 i ((v ⨯₃ w) · σ)`.

## Implementation notes

### Indexing by `Fin 3` rather than by `Fin 1 ⊕ Fin 3`

In the physics literature one usually meets the four-element family `σ^μ = (σ^0, σ^1, σ^2, σ^3)`
with `σ^0 = 1`, indexed so that it transforms as a spacetime four-vector. That indexing is not the
right primitive here: `σ^0` is *already* available as `1`, and the statements that matter
mathematically — tracelessness, `det σᵃ = -1`, trace-orthogonality with normalisation `2 δᵃᵇ`, the
commutation relations, and the fact that `{i σᵃ}` spans the traceless anti-Hermitian `2 × 2`
matrices, i.e. `𝔰𝔲(2)` — are all false or degenerate for `σ^0`. Indexing by `Fin 3` therefore lets
every lemma below be stated uniformly in `a : Fin 3`, with no case that has to be excluded.

The relation to the identity is kept: `Matrix.pauli_mul_self` gives `σᵃ * σᵃ = 1`,
`Matrix.pauli_mul_add_mul_pauli` gives `{σᵃ, σᵇ} = 2 δᵃᵇ • 1`, and the physics four-family is
available as `Matrix.pauliSum`, defined as `Sum.elim (fun _ => 1) pauli`, with
`Matrix.pauliSum_inl` and `Matrix.pauliSum_inr` relating the two.

### The commutation relation

The relation is usually written `⁅σᵃ, σᵇ⁆ = 2 i εᵃᵇᶜ σᶜ`. There is no Levi-Civita symbol in
Mathlib, so the general statement is given in the equivalent index-free form
`Matrix.pauliVector_commutator`, contracting both free indices against vectors and using the cross
product in place of `ε`; the three cyclic instances are also available individually as
`Matrix.pauli_commutator_zero_one` and friends.
-/

@[expose] public section

open Complex

namespace Matrix

/-- The Pauli matrices `σ₁`, `σ₂`, `σ₃`, indexed by `Fin 3`. Note that the indexing is
zero-based, so `pauli 0`, `pauli 1` and `pauli 2` are the matrices written `σ₁`, `σ₂` and `σ₃`
in the physics literature. -/
def pauli : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => !![0, 1; 1, 0]
  | 1 => !![0, -I; I, 0]
  | 2 => !![1, 0; 0, -1]

@[simp] theorem pauli_zero : pauli 0 = !![0, 1; 1, 0] := rfl

@[simp] theorem pauli_one : pauli 1 = !![0, -I; I, 0] := rfl

@[simp] theorem pauli_two : pauli 2 = !![1, 0; 0, -1] := rfl

/-- The four-element family `σ^μ = (1, σ₁, σ₂, σ₃)` used in physics, where the `Fin 1` summand
carries the identity matrix. See the module docstring for why `Matrix.pauli` rather than this is
the primitive. -/
def pauliSum : Fin 1 ⊕ Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  Sum.elim (fun _ => 1) pauli

@[simp] theorem pauliSum_inl (i : Fin 1) : pauliSum (Sum.inl i) = 1 := rfl

@[simp] theorem pauliSum_inr (a : Fin 3) : pauliSum (Sum.inr a) = pauli a := rfl

/-! ### Adjoints -/

/-- The Pauli matrices are self-adjoint. -/
@[simp]
theorem conjTranspose_pauli (a : Fin 3) : (pauli a)ᴴ = pauli a := by
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauli, Matrix.conjTranspose_apply, Complex.star_def]

/-- The Pauli matrices are Hermitian. -/
theorem isHermitian_pauli (a : Fin 3) : (pauli a).IsHermitian :=
  conjTranspose_pauli a

/-! ### Traces, squares and determinants -/

/-- The Pauli matrices are traceless. -/
@[simp]
theorem trace_pauli (a : Fin 3) : trace (pauli a) = 0 := by
  fin_cases a <;> simp [pauli, Matrix.trace_fin_two_of]

/-- The Pauli matrices are involutions. -/
@[simp]
theorem pauli_mul_self (a : Fin 3) : pauli a * pauli a = 1 := by
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauli, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

/-- The Pauli matrices are their own inverses. -/
instance invertiblePauli (a : Fin 3) : Invertible (pauli a) :=
  ⟨pauli a, pauli_mul_self a, pauli_mul_self a⟩

@[simp]
theorem invOf_pauli (a : Fin 3) : ⅟(pauli a) = pauli a := rfl

/-- The Pauli matrices have determinant `-1`. -/
@[simp]
theorem det_pauli (a : Fin 3) : (pauli a).det = -1 := by
  fin_cases a <;> simp [pauli, Matrix.det_fin_two_of, Complex.I_mul_I]

/-- The trace-orthogonality relation `Tr (σᵃ σᵇ) = 2 δᵃᵇ` for the Pauli matrices. This is the
normalisation from which the `𝔰𝔲(2)` relation `Tr (Tᵃ Tᵇ) = δᵃᵇ / 2` for `Tᵃ = σᵃ / 2` follows;
see `Matrix.trace_half_pauli_mul_half_pauli`. -/
theorem trace_pauli_mul_pauli (a b : Fin 3) :
    trace (pauli a * pauli b) = if a = b then 2 else 0 := by
  fin_cases a <;> fin_cases b <;>
    simp [pauli, Matrix.trace_fin_two, Complex.I_mul_I] <;> ring_nf

/-- The trace-normalisation `Tr (Tᵃ Tᵇ) = δᵃᵇ / 2` of the generators `Tᵃ = σᵃ / 2` of `𝔰𝔲(2)`. -/
theorem trace_half_pauli_mul_half_pauli (a b : Fin 3) :
    trace (((2 : ℂ)⁻¹ • pauli a) * ((2 : ℂ)⁻¹ • pauli b)) = if a = b then (2 : ℂ)⁻¹ else 0 := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, trace_smul, trace_pauli_mul_pauli, smul_eq_mul]
  split <;> norm_num

/-! ### Commutation relations -/

/-- The anticommutation relation `{σᵃ, σᵇ} = 2 δᵃᵇ • 1` for the Pauli matrices. -/
theorem pauli_mul_add_mul_pauli (a b : Fin 3) :
    pauli a * pauli b + pauli b * pauli a = (if a = b then (2 : ℂ) else 0) • 1 := by
  fin_cases a <;> fin_cases b <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauli, Complex.I_mul_I] <;> ring_nf

theorem pauli_anticommutator_zero_one : pauli 0 * pauli 1 + pauli 1 * pauli 0 = 0 := by
  rw [pauli_mul_add_mul_pauli 0 1]
  norm_num

theorem pauli_anticommutator_zero_two : pauli 0 * pauli 2 + pauli 2 * pauli 0 = 0 := by
  rw [pauli_mul_add_mul_pauli 0 2]
  norm_num
  decide

theorem pauli_anticommutator_one_two : pauli 1 * pauli 2 + pauli 2 * pauli 1 = 0 := by
  rw [pauli_mul_add_mul_pauli 1 2]
  norm_num
  decide

theorem pauli_commutator_zero_one :
    pauli 0 * pauli 1 - pauli 1 * pauli 0 = (2 * I) • pauli 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauli] <;> ring_nf

theorem pauli_commutator_one_two :
    pauli 1 * pauli 2 - pauli 2 * pauli 1 = (2 * I) • pauli 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauli] <;> ring_nf

theorem pauli_commutator_two_zero :
    pauli 2 * pauli 0 - pauli 0 * pauli 2 = (2 * I) • pauli 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauli] <;> ring_nf <;> simp [Complex.I_sq]

/-! ### Pauli vectors -/

/-- The matrix `v · σ = ∑ i, v i • σᵢ` associated with a vector `v`. -/
def pauliVector (v : Fin 3 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ i : Fin 3, v i • pauli i

theorem pauliVector_apply (v : Fin 3 → ℂ) :
    pauliVector v = v 0 • pauli 0 + v 1 • pauli 1 + v 2 • pauli 2 := by
  simp [pauliVector, Fin.sum_univ_three]

/-- The anticommutation relation for Pauli vectors: `{v · σ, w · σ} = 2 (v ⬝ᵥ w) • 1`. -/
theorem pauliVector_anticommutator (v w : Fin 3 → ℂ) :
    pauliVector v * pauliVector w + pauliVector w * pauliVector v =
      (2 * (v ⬝ᵥ w)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have h : pauliVector v * pauliVector w + pauliVector w * pauliVector v =
      (v 0 * w 0) • (pauli 0 * pauli 0 + pauli 0 * pauli 0) +
      (v 1 * w 1) • (pauli 1 * pauli 1 + pauli 1 * pauli 1) +
      (v 2 * w 2) • (pauli 2 * pauli 2 + pauli 2 * pauli 2) +
      (v 0 * w 1 + v 1 * w 0) • (pauli 0 * pauli 1 + pauli 1 * pauli 0) +
      (v 0 * w 2 + v 2 * w 0) • (pauli 0 * pauli 2 + pauli 2 * pauli 0) +
      (v 1 * w 2 + v 2 * w 1) • (pauli 1 * pauli 2 + pauli 2 * pauli 1) := by
    simp only [pauliVector, Fin.sum_univ_three, add_mul, mul_add, Algebra.smul_mul_assoc,
      Algebra.mul_smul_comm]
    module
  rw [h]
  simp only [pauli_mul_self, pauli_anticommutator_zero_one, pauli_anticommutator_zero_two,
    pauli_anticommutator_one_two, smul_zero, add_zero, dotProduct, Fin.sum_univ_three]
  module

/-- The commutation relation for Pauli vectors: `⁅v · σ, w · σ⁆ = 2 i ((v ⨯₃ w) · σ)`. This is the
index-free form of `⁅σᵃ, σᵇ⁆ = 2 i εᵃᵇᶜ σᶜ`. -/
theorem pauliVector_commutator (v w : Fin 3 → ℂ) :
    pauliVector v * pauliVector w - pauliVector w * pauliVector v =
      (2 * I) • pauliVector (v ⨯₃ w) := by
  have h : pauliVector v * pauliVector w - pauliVector w * pauliVector v =
      (v 0 * w 1 - v 1 * w 0) • (pauli 0 * pauli 1 - pauli 1 * pauli 0) +
      (v 2 * w 0 - v 0 * w 2) • (pauli 2 * pauli 0 - pauli 0 * pauli 2) +
      (v 1 * w 2 - v 2 * w 1) • (pauli 1 * pauli 2 - pauli 2 * pauli 1) := by
    simp only [pauliVector, Fin.sum_univ_three, add_mul, mul_add, Algebra.smul_mul_assoc,
      Algebra.mul_smul_comm]
    module
  rw [h, pauli_commutator_zero_one, pauli_commutator_two_zero, pauli_commutator_one_two]
  simp only [pauliVector, Fin.sum_univ_three, cross_apply, Fin.isValue, cons_val_zero, cons_val_one,
    cons_val]
  module

/-- The product formula for Pauli vectors: `(v · σ) (w · σ) = (v ⬝ᵥ w) • 1 + i ((v ⨯₃ w) · σ)`. -/
theorem pauliVector_mul_pauliVector (v w : Fin 3 → ℂ) :
    pauliVector v * pauliVector w =
      (v ⬝ᵥ w) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + I • pauliVector (v ⨯₃ w) := by
  have h2 : (2 : ℂ) • (pauliVector v * pauliVector w) =
      (pauliVector v * pauliVector w + pauliVector w * pauliVector v) +
      (pauliVector v * pauliVector w - pauliVector w * pauliVector v) := by
    rw [two_smul]; abel
  refine smul_right_injective _ (two_ne_zero (α := ℂ)) ?_
  simp only
  rw [h2, pauliVector_anticommutator, pauliVector_commutator]
  module

/-! ### The Lie bracket form of the commutation relations -/

section LieBracket

attribute [local instance 100] LieRing.ofAssociativeRing

theorem lie_pauli_zero_one : ⁅pauli 0, pauli 1⁆ = (2 * I) • pauli 2 := by
  rw [LieRing.of_associative_ring_bracket]; exact pauli_commutator_zero_one

theorem lie_pauli_one_two : ⁅pauli 1, pauli 2⁆ = (2 * I) • pauli 0 := by
  rw [LieRing.of_associative_ring_bracket]; exact pauli_commutator_one_two

theorem lie_pauli_two_zero : ⁅pauli 2, pauli 0⁆ = (2 * I) • pauli 1 := by
  rw [LieRing.of_associative_ring_bracket]; exact pauli_commutator_two_zero

/-- The commutation relation for Pauli vectors, in Lie-bracket form. -/
theorem lie_pauliVector (v w : Fin 3 → ℂ) :
    ⁅pauliVector v, pauliVector w⁆ = (2 * I) • pauliVector (v ⨯₃ w) := by
  rw [LieRing.of_associative_ring_bracket]; exact pauliVector_commutator v w

end LieBracket

end Matrix
