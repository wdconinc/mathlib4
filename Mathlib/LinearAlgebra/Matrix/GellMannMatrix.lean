/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Gell-Mann matrices

This file defines the eight Gell-Mann matrices as a family
`Matrix.gellMann : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ` and proves their basic algebraic
properties: they are Hermitian, traceless, trace-orthogonal with normalisation `2 δᵃᵇ`, and
their squares sum to `(16/3) • 1`.

They are the three-dimensional analogue of `Matrix.pauli`, and play the same role for `𝔰𝔲(3)`
that the Pauli matrices play for `𝔰𝔲(2)`: the matrices `Tᵃ = λᵃ / 2` are a basis of the
traceless Hermitian `3 × 3` matrices normalised so that `Tr (Tᵃ Tᵇ) = δᵃᵇ / 2`.

## Main definitions

  * `Matrix.gellMann`: the eight Gell-Mann matrices `λ¹, …, λ⁸`, indexed by `Fin 8`.

## Main statements

  * `Matrix.isHermitian_gellMann`: each `λᵃ` is Hermitian.
  * `Matrix.trace_gellMann`: each `λᵃ` is traceless.
  * `Matrix.trace_gellMann_mul_gellMann`: the trace-orthogonality relation
    `Tr (λᵃ λᵇ) = 2 δᵃᵇ`.
  * `Matrix.trace_half_gellMann_mul_half_gellMann`: the `𝔰𝔲(3)` normalisation
    `Tr (Tᵃ Tᵇ) = δᵃᵇ / 2` for `Tᵃ = λᵃ / 2`.
  * `Matrix.sum_gellMann_mul_gellMann`: the Casimir relation `∑ a, λᵃ λᵃ = (16/3) • 1`, and
    `Matrix.sum_half_gellMann_mul_half_gellMann`, its form `∑ a, Tᵃ Tᵃ = (4/3) • 1` for
    `Tᵃ = λᵃ / 2`, exhibiting the quadratic Casimir `C_F = 4/3` of the fundamental
    representation of `𝔰𝔲(3)`.

## Implementation notes

### Indexing by `Fin 8`

The indexing is zero-based, so `gellMann 0, …, gellMann 7` are the matrices written
`λ¹, …, λ⁸` in the physics literature. This matches the convention of `Matrix.pauli`.

### The eighth matrix and `Real.sqrt`

The matrix `λ⁸ = (1/√3) diag (1, 1, -2)` is the only one whose entries are not Gaussian
integers, and it is the reason this file depends on `Real.sqrt`. The normalisation `1/√3` is
forced by requiring `Tr (λ⁸ λ⁸) = 2` like all the others; without it the family would not be
trace-orthonormal and `Matrix.trace_gellMann_mul_gellMann` would have to carry an exceptional
case. The single arithmetic fact about `√3` that the proofs need is isolated as
`Matrix.inv_ofReal_sqrt_three_sq`.

### The structure constants

The relations `⁅λᵃ, λᵇ⁆ = 2 i fᵃᵇᶜ λᶜ` and `{λᵃ, λᵇ} = (4/3) δᵃᵇ + 2 dᵃᵇᶜ λᶜ` require the
`𝔰𝔲(3)` structure constants `f` and `d`, which are not defined here; only the relations that
are index-free or diagonal in `a, b` are proved.
-/

@[expose] public section

open Complex

namespace Matrix

/-- The Gell-Mann matrices `λ¹, …, λ⁸`, indexed by `Fin 8`. Note that the indexing is
zero-based, so `gellMann 0, …, gellMann 7` are the matrices written `λ¹, …, λ⁸` in the
physics literature; in particular `gellMann 7` is the diagonal matrix
`(1/√3) diag (1, 1, -2)`. -/
noncomputable def gellMann : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ
  | 0 => !![0, 1, 0; 1, 0, 0; 0, 0, 0]
  | 1 => !![0, -I, 0; I, 0, 0; 0, 0, 0]
  | 2 => !![1, 0, 0; 0, -1, 0; 0, 0, 0]
  | 3 => !![0, 0, 1; 0, 0, 0; 1, 0, 0]
  | 4 => !![0, 0, -I; 0, 0, 0; I, 0, 0]
  | 5 => !![0, 0, 0; 0, 0, 1; 0, 1, 0]
  | 6 => !![0, 0, 0; 0, 0, -I; 0, I, 0]
  | 7 => (Real.sqrt 3 : ℂ)⁻¹ • !![1, 0, 0; 0, 1, 0; 0, 0, -2]

@[simp] theorem gellMann_zero : gellMann 0 = !![0, 1, 0; 1, 0, 0; 0, 0, 0] := rfl

@[simp] theorem gellMann_one : gellMann 1 = !![0, -I, 0; I, 0, 0; 0, 0, 0] := rfl

@[simp] theorem gellMann_two : gellMann 2 = !![1, 0, 0; 0, -1, 0; 0, 0, 0] := rfl

@[simp] theorem gellMann_three : gellMann 3 = !![0, 0, 1; 0, 0, 0; 1, 0, 0] := rfl

@[simp] theorem gellMann_four : gellMann 4 = !![0, 0, -I; 0, 0, 0; I, 0, 0] := rfl

@[simp] theorem gellMann_five : gellMann 5 = !![0, 0, 0; 0, 0, 1; 0, 1, 0] := rfl

@[simp] theorem gellMann_six : gellMann 6 = !![0, 0, 0; 0, 0, -I; 0, I, 0] := rfl

@[simp] theorem gellMann_seven :
    gellMann 7 = (Real.sqrt 3 : ℂ)⁻¹ • !![1, 0, 0; 0, 1, 0; 0, 0, -2] := rfl

/-! ### The arithmetic of `√3` -/

/-- The square of `(√3 : ℂ)⁻¹` is `3⁻¹`. This is the only fact about `√3` used below. -/
theorem inv_ofReal_sqrt_three_sq : ((Real.sqrt 3 : ℂ)⁻¹) ^ 2 = 3⁻¹ := by
  rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

/-! ### Adjoints -/

/-- The Gell-Mann matrices are self-adjoint. -/
@[simp]
theorem conjTranspose_gellMann (a : Fin 8) : (gellMann a)ᴴ = gellMann a := by
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [gellMann, Matrix.conjTranspose_apply, Complex.star_def]

/-- The Gell-Mann matrices are Hermitian. -/
theorem isHermitian_gellMann (a : Fin 8) : (gellMann a).IsHermitian :=
  conjTranspose_gellMann a

/-! ### Traces -/

/-- The Gell-Mann matrices are traceless. -/
@[simp]
theorem trace_gellMann (a : Fin 8) : trace (gellMann a) = 0 := by
  fin_cases a <;> simp [gellMann, Matrix.trace_fin_three]
  ring

/-- The trace-orthogonality relation `Tr (λᵃ λᵇ) = 2 δᵃᵇ` for the Gell-Mann matrices. This is
the normalisation from which the `𝔰𝔲(3)` relation `Tr (Tᵃ Tᵇ) = δᵃᵇ / 2` for `Tᵃ = λᵃ / 2`
follows; see `Matrix.trace_half_gellMann_mul_half_gellMann`. -/
theorem trace_gellMann_mul_gellMann (a b : Fin 8) :
    trace (gellMann a * gellMann b) = if a = b then 2 else 0 := by
  have h1 : ((Real.sqrt 3 : ℂ)⁻¹) ^ 2 = 3⁻¹ := inv_ofReal_sqrt_three_sq
  fin_cases a <;> fin_cases b
  all_goals
    simp [gellMann, Matrix.trace_fin_three, Complex.I_mul_I, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try ring_nf)
  all_goals (try simp only [h1])
  all_goals (try norm_num)

/-- The trace-normalisation `Tr (Tᵃ Tᵇ) = δᵃᵇ / 2` of the generators `Tᵃ = λᵃ / 2` of
`𝔰𝔲(3)`. -/
theorem trace_half_gellMann_mul_half_gellMann (a b : Fin 8) :
    trace (((2 : ℂ)⁻¹ • gellMann a) * ((2 : ℂ)⁻¹ • gellMann b)) =
      if a = b then (2 : ℂ)⁻¹ else 0 := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, trace_smul, trace_gellMann_mul_gellMann,
    smul_eq_mul]
  split <;> norm_num

/-! ### The quadratic Casimir -/

/-- The Casimir relation `∑ a, λᵃ λᵃ = (16/3) • 1` for the Gell-Mann matrices. -/
theorem sum_gellMann_mul_gellMann :
    ∑ a : Fin 8, gellMann a * gellMann a =
      ((16 : ℂ) / 3) • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  have h1 : ((Real.sqrt 3 : ℂ)⁻¹) ^ 2 = 3⁻¹ := inv_ofReal_sqrt_three_sq
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [Fin.sum_univ_eight, gellMann, Matrix.sum_apply, Matrix.mul_apply,
      Fin.sum_univ_three, Complex.I_mul_I, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  all_goals (try ring_nf)
  all_goals (try simp only [h1])
  all_goals (try norm_num)

/-- The quadratic Casimir of the fundamental representation of `𝔰𝔲(3)`:
`∑ a, Tᵃ Tᵃ = (4/3) • 1` for `Tᵃ = λᵃ / 2`, i.e. `C_F = 4/3`. -/
theorem sum_half_gellMann_mul_half_gellMann :
    ∑ a : Fin 8, ((2 : ℂ)⁻¹ • gellMann a) * ((2 : ℂ)⁻¹ • gellMann a) =
      ((4 : ℂ) / 3) • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  have h : ∀ A : Matrix (Fin 3) (Fin 3) ℂ,
      ((2 : ℂ)⁻¹ • A) * ((2 : ℂ)⁻¹ • A) = (4 : ℂ)⁻¹ • (A * A) := by
    intro A
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    norm_num
  simp only [h, ← Finset.smul_sum, sum_gellMann_mul_gellMann, smul_smul]
  norm_num

end Matrix
