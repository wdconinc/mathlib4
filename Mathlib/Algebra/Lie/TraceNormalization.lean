/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Algebra.Lie.Casimir

/-!
# Trace normalization of a family of Lie algebra elements

Let `L` be a Lie algebra over a commutative ring `R`, let `M` be a representation of `L` with
associated morphism `φ = LieModule.toEnd R L M`, and let `T : ι → L` be a finite family of
elements of `L`. Say that `T` is *trace normalized with index `t`* for `M` when

`traceForm R L M (T a) (T b) = if a = b then t else 0`,

that is, when the family is orthogonal for the trace form of `M` with common squared length `t`.

If in addition the associated quadratic Casimir element `∑ a, φ (T a) ∘ₗ φ (T a)` acts as a
scalar `c` on `M`, then `t` and `c` are not independent: taking `LinearMap.trace` of the Casimir
element evaluates in two ways, giving

`finrank R M * c = t * card ι`.

This is a counting relation. It is basis-free, uses no explicit realisation of `L` by matrices,
and holds over an arbitrary commutative ring. In the physics literature the two constants are the
*index* `T_F` and the *quadratic Casimir* `C_F` of the representation, and the relation is the
standard `finrank · C_F = T_F · dim L`; for the defining representation of `𝔰𝔲(N)` one has
`card ι = N ^ 2 - 1` and `finrank = N`, whence `C_F = T_F * (N ^ 2 - 1) / N`.

Specialising `M` to the adjoint representation `L` replaces the trace form by the Killing form,
since `killingForm R L` is by definition `LieModule.traceForm R L L`, and yields the corresponding
relation for the adjoint constants.

## Main definitions

* `LieModule.IsTraceNormalized`: the predicate that a finite family `T : ι → L` is orthogonal for
  the trace form of `M` with common diagonal value `t`.

## Main statements

* `LieModule.finrank_mul_of_isCasimirScalar`: **the index relation.** A trace-normalized family
  whose Casimir element is the scalar `c` satisfies `finrank R M * c = t * card ι`.
* `LieModule.casimirScalar_eq_of_isTraceNormalized`: over a field, the same relation solved for
  the Casimir scalar.
* `LieModule.finrank_mul_of_isCasimirScalar_adjoint`: the specialisation to the adjoint
  representation, stated in terms of `killingForm`.
* `LieModule.commute_toEnd_casimirOfBasis_of_isTraceNormalized`: a basis that is trace normalized
  with index `1` has central Casimir element.

## Implementation notes

The Casimir element used here is `LieModule.casimir R L M T T`, the sum `∑ a, φ (T a) ∘ₗ φ (T a)`
in which an adjoint index is contracted with itself. As explained in the implementation notes of
`Mathlib/Algebra/Lie/Casimir.lean`, that expression deserves the name "Casimir" only relative to
an invariant form for which the family is orthonormal. Trace normalization with index `t` is
exactly that hypothesis for the form `t⁻¹ • traceForm R L M`, and the hypothesis is stated
explicitly wherever it is used rather than built into the definition.

The relation itself, however, needs no such interpretation: it is a formal consequence of the two
displayed hypotheses, which is why `LieModule.finrank_mul_of_isCasimirScalar` assumes no
invertibility of `t`, no nondegeneracy, and no semisimplicity.
-/

@[expose] public section

open Module (finrank)
open LinearMap (trace)

namespace LieModule

attribute [local instance 100] LieRing.ofAssociativeRing

section General

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A finite family `T : ι → L` is *trace normalized with index `t`* for the representation `M`
when it is orthogonal for the trace form of `M`, with common diagonal value `t`:

`traceForm R L M (T a) (T b) = if a = b then t else 0`.

In the physics literature `t` is the index `T_F` of the representation; the usual normalization
of the generators of `𝔰𝔲(N)` in the defining representation is `t = 1 / 2`. -/
def IsTraceNormalized (T : ι → L) (t : R) : Prop :=
  ∀ a b, traceForm R L M (T a) (T b) = if a = b then t else 0

variable {R L M}

omit [Fintype ι] in
lemma IsTraceNormalized.apply_self {T : ι → L} {t : R} (h : IsTraceNormalized R L M T t) (a : ι) :
    traceForm R L M (T a) (T a) = t := by
  simpa using h a a

omit [Fintype ι] in
lemma IsTraceNormalized.apply_ne {T : ι → L} {t : R} (h : IsTraceNormalized R L M T t) {a b : ι}
    (hab : a ≠ b) : traceForm R L M (T a) (T b) = 0 := by
  simpa [hab] using h a b

/-- The trace of the Casimir element of a trace-normalized family is `card ι * t`. -/
lemma IsTraceNormalized.sum_diag {T : ι → L} {t : R} (h : IsTraceNormalized R L M T t) :
    ∑ a, traceForm R L M (T a) (T a) = (Fintype.card ι : R) * t := by
  rw [Finset.sum_congr rfl fun a _ => h.apply_self a, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]

/-- **The index relation.**

If a finite family `T : ι → L` is trace normalized with index `t` for the representation `M`, and
its quadratic Casimir element acts on `M` as the scalar `c`, then

`finrank R M * c = t * card ι`.

Both sides compute `LinearMap.trace R M` of the Casimir element `∑ a, φ (T a) ∘ₗ φ (T a)`: the
left-hand side from the assumption that it is the scalar `c`, the right-hand side from the
trace normalization of `T`.

For the defining representation of `𝔰𝔲(N)`, where `card ι = N ^ 2 - 1` and `finrank R M = N`,
this is the relation `C_F = T_F * (N ^ 2 - 1) / N` between the index and the quadratic Casimir;
see `LieModule.casimirScalar_eq_of_isTraceNormalized` for the divided form. -/
theorem finrank_mul_of_isCasimirScalar [Module.Free R M] [Module.Finite R M]
    {T : ι → L} {t c : R}
    (ht : IsTraceNormalized R L M T t) (hc : IsCasimirScalar R L M T T c) :
    (finrank R M : R) * c = t * (Fintype.card ι : R) := by
  have h := congrArg (trace R M) hc
  rw [trace_casimir, map_smul, LinearMap.trace_one, smul_eq_mul, ht.sum_diag] at h
  linear_combination -h

/-- The index relation for the adjoint representation, in terms of the Killing form.

This is `LieModule.finrank_mul_of_isCasimirScalar` at `M = L`, using that `killingForm R L` is by
definition `LieModule.traceForm R L L`. In the physics literature the constant `c` here is the
adjoint Casimir `C_A`. -/
theorem finrank_mul_of_isCasimirScalar_adjoint [Module.Free R L] [Module.Finite R L]
    {T : ι → L} {t c : R}
    (ht : ∀ a b, killingForm R L (T a) (T b) = if a = b then t else 0)
    (hc : IsCasimirScalar R L L T T c) :
    (finrank R L : R) * c = t * (Fintype.card ι : R) :=
  finrank_mul_of_isCasimirScalar ht hc

/-- A basis that is trace normalized with index `1` has central quadratic Casimir element.

The invariant form implicit in the contraction `∑ a, φ (T a) ∘ₗ φ (T a)` is the trace form itself,
which is invariant by `LieModule.traceForm_lieInvariant`, and the basis is orthonormal for it by
hypothesis. -/
theorem commute_toEnd_casimirOfBasis_of_isTraceNormalized (b : Module.Basis ι R L)
    (hb : IsTraceNormalized R L M b 1) (x : L) :
    Commute (toEnd R L M x) (casimirOfBasis R L M b) :=
  commute_toEnd_casimirOfBasis M (traceForm_lieInvariant R L M) b hb x

end General

section Field

variable {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [Module.Free K M] [Module.Finite K M]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Over a field, the index relation solved for the Casimir scalar:

`c = t * card ι / finrank K M`.

For the defining representation of `𝔰𝔲(N)` this reads `C_F = T_F * (N ^ 2 - 1) / N`. -/
theorem casimirScalar_eq_of_isTraceNormalized {T : ι → L} {t c : K}
    (ht : IsTraceNormalized K L M T t) (hc : IsCasimirScalar K L M T T c)
    (hM : (finrank K M : K) ≠ 0) :
    c = t * (Fintype.card ι : K) / (finrank K M : K) := by
  rw [eq_div_iff hM]
  linear_combination finrank_mul_of_isCasimirScalar ht hc

end Field

end LieModule
